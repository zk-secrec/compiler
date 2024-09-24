{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE LambdaCase #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Main (main) where

import Basic.Location (Location (..), Position (..))
import Basic.Message
  ( Message,
    MessageLevel (..),
    getMsgLevel,
    getMsgLocs,
    getMsgText,
    getSortedMsgs,
    prettyMessage,
  )
import qualified Compiler
import Compiler
  ( TypeCheckingResult,
    FileSystemM (..),
    SourceFileHandle (..),
    messages,
    typedProgram,
    parse,
  )
import Control.Applicative ((<|>))
import Control.Concurrent (forkIO)
import Control.Concurrent.STM.TChan (TChan, newTChan, readTChan, writeTChan)
import qualified Control.Exception as E
import Control.Lens ((&), (.~), (^.), to)
import Control.Monad (forever, void, when)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader.Class (MonadReader, ask)
import Control.Monad.STM (atomically)
import Control.Monad.Trans.Except (runExceptT, throwE)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT (..))
import Data.Either (lefts, rights)
import Data.IORef (IORef, newIORef, modifyIORef, readIORef)
import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe, maybeToList, catMaybes)
import qualified Data.Rope.UTF16 as Rope
import qualified Data.Text as T
import qualified Data.Text.Encoding as TextEncoding
import qualified Data.Text.IO as T
import Index (SymbolInfo(..), indexProgram, symbolLookup)
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Server (getVirtualFiles, notificationHandler, requestHandler)
import qualified Language.LSP.Server as L
import qualified Language.LSP.Types as L
import qualified Language.LSP.Types.Lens as L hiding
  ( publishDiagnostics,
    textDocumentSync,
  )
import Language.LSP.VFS as VFS
  ( VirtualFile (..),
    vfsMap,
    virtualFileText,
    virtualFileVersion,
  )
import Parser.Lexer (tokenEndPos)
import Parser.Syntax (Module, LProgram)
import Support.Pretty (render, renderStrictText)
import System.Console.CmdArgs
import System.Directory (doesFileExist)
import System.Exit (die)
import System.FilePath (splitFileName, takeFileName)
import System.IO (hPutStrLn, stderr)
import Text.Printf (printf)
import Version

programName :: String
programName = "zksc-language-server"

data ServerArgs = ServerArgs
  { debugArg :: Bool
  , serveArg :: Bool
  } deriving (Show, Data, Typeable)

serverArgs :: ServerArgs
serverArgs = ServerArgs
  { debugArg = def &= help "Log debug messages."
                   &= name "debug"
                   &= typFile
                   &= explicit
  , serveArg = def &= help "Start a server"
                   &= name "serve"
  }
  &= summary ("ZK-SecreC language server " ++ version)
  &= program programName

-- We could technically keep this state in the env of LspT but that is designed
-- for the configuration that is visible in your editor so it seems cleaner to
-- have our own environment.
data ServerEnv
  = ServerEnv
  { debug :: Bool
  , tcCache :: IORef (Map.Map L.NormalizedUri (Int, TypeCheckingResult))
  }

newtype ServerM a
  = ServerM { unServerM :: ReaderT ServerEnv (L.LspM ()) a }
  deriving (Applicative,
            Functor,
            Monad,
            MonadIO,
            MonadReader ServerEnv,
            MonadUnliftIO,
            L.MonadLsp ())

vfsFindFile :: FilePath -> ServerM (Maybe VirtualFile)
vfsFindFile fileName = do
  virtualFiles <- getVirtualFiles
  let vfs = vfsMap virtualFiles
  let fileNamesWithURIs = mapMaybe getURIFileName $ Map.keys vfs
  let virtualFile = do
        (_, uri) <- find ((== fileName) . fst) fileNamesWithURIs
        Map.lookup uri vfs
  return virtualFile
  where
    getURIFileName uri = do
      L.NormalizedFilePath _ path <- L.uriToNormalizedFilePath uri
      let (_, fileName) = splitFileName path
      Just (fileName, uri)

instance FileSystemM ServerM where
  fsFindFile userSearchPaths systemSearchPaths fileName = do
    virtFile <- vfsFindFile fileName
    realFile <- liftIO $ fsFindFile userSearchPaths systemSearchPaths fileName
    return $ (virtFile *> Just (SourceOnDisk fileName)) <|> realFile

  fsReadFile (SourceInMemory _ bs) = return $ TextEncoding.decodeUtf8 bs
  fsReadFile (SourceOnDisk fileName) = do
    maybeVirtFile <- vfsFindFile fileName
    case maybeVirtFile of
      Just virtualFile -> return $ virtualFileText virtualFile
      Nothing -> liftIO $ do
        exists <- doesFileExist fileName
        if exists then
          T.readFile fileName
        else
          ioError $ userError $
          "FileSystemM ServerM fsReadfile: " ++ fileName

  fsReadFileByteString fileName =
    TextEncoding.encodeUtf8 <$> fsReadFile (SourceOnDisk fileName)

logDebug :: String -> ServerM ()
logDebug msg = do
  env <- ask
  when (debug env) $
    liftIO $ hPutStrLn stderr $ "[ZKSCLS] " ++ msg

newtype ReactorInput = ReactorAction (IO ())

reactor :: TChan ReactorInput -> Bool -> IO ()
reactor inp debug = do
  when debug $
    hPutStrLn stderr "[ZKSCLS] Started the reactor thread"
  forever $ liftIO $ do
    ReactorAction act <- atomically $ readTChan inp
    act

syncOptions :: L.TextDocumentSyncOptions
syncOptions = L.TextDocumentSyncOptions
  { L._openClose = Just True
  , L._change = Just L.TdSyncIncremental
  , L._willSave = Just False
  , L._willSaveWaitUntil = Just False
  , L._save = Just $ L.InR $ L.SaveOptions $ Just False
  }

lspOptions :: L.Options
lspOptions = L.defaultOptions { L.textDocumentSync = Just syncOptions }

run :: ServerArgs -> IO ()
run ServerArgs{..} = flip E.catches handlers $ do
  rin  <- atomically newTChan :: IO (TChan ReactorInput)

  emptyCache <- newIORef Map.empty

  let serverEnv = ServerEnv
        { debug = debugArg
        , tcCache = emptyCache
        }
  let serverDefinition = L.ServerDefinition
        { defaultConfig = ()
        , onConfigurationChange = \_ _ -> Right ()
        , doInitialize = \env _ ->
            forkIO (reactor rin debugArg) >>
            pure (Right env)
        , staticHandlers = lspHandlers rin serverEnv
        , interpretHandler = \env ->
            L.Iso
            (\act -> L.runLspT env (runReaderT (unServerM act) serverEnv))
            liftIO
        , options = lspOptions
        }

  hPutStrLn stderr "Starting ZK-SecreC language server"
  void $ L.runServer serverDefinition

  where
    handlers = [ E.Handler ioExcept
               , E.Handler someExcept
               ]
    ioExcept (e :: E.IOException) = die $ show e
    someExcept (e :: E.SomeException) = die $ show e

locToRange :: Location -> Maybe L.Range
locToRange NoLocation = Nothing
locToRange Location{..} =
  -- Indices start from 0 in LSP and 1 in zkscc
  Just $ L.Range
  (L.Position (_locFirstLine - 1) (_locFirstCol - 1))
  (L.Position (_locLastLine - 1) (_locLastCol - 1))

diagnostic :: L.DiagnosticSeverity -> L.Range -> T.Text -> L.Diagnostic
diagnostic severity loc msg =
  L.Diagnostic
  { L._range = loc
  , L._severity = Just severity
  , L._code = Nothing
  , L._source = Just $ T.pack programName
  , L._message = msg
  , L._tags = Nothing
  , L._relatedInformation  = Nothing
  }

diagError :: L.Range -> T.Text -> L.Diagnostic
diagError = diagnostic L.DsError

-- Evaluates to pair of notifications, diagnostics for the given file
messageToLSP :: FilePath -> Message -> ([T.Text], [L.Diagnostic])
messageToLSP fileName msg =
  case getMsgLocs msg of
    [] -> ([txt], [])
    locs@(_ : _) ->
      let notsOrDiags = catMaybes $ flip map locs $ \loc -> case locToRange loc of
            Nothing -> Just $ Left txt
            Just range | fileName == _locFilename loc ->
              Just $ Right $ diagnostic severity range txt
            _ -> Nothing
      in
      (lefts notsOrDiags, rights notsOrDiags)
  where
    txt = renderStrictText $ getMsgText msg
    severity = case getMsgLevel msg of
      MsgWarning -> L.DsWarning
      MsgError -> L.DsError
      MsgFatal -> L.DsError
      MsgDebug -> L.DsInfo

sendNotification :: T.Text -> ServerM ()
sendNotification msg =
  L.sendNotification L.SWindowShowMessage (L.ShowMessageParams L.MtInfo msg)

sendDiagnostics :: L.NormalizedUri -> Int -> [L.Diagnostic] -> ServerM ()
sendDiagnostics fileUri version diags =
  L.publishDiagnostics
  (length diags)
  fileUri
  (Just version)
  (partitionBySource diags)

getCmdOptions :: L.NormalizedUri -> Compiler.CmdOptions
getCmdOptions uri =
  Compiler.defaultCmdOptions
  & Compiler.input .~ fileName
  & Compiler.librarySearchPaths .~ workingDir
  where
    L.NormalizedUri _ filePath = uri
    (_, fileName) = splitFileName $ T.unpack filePath
    workingDir = maybeToList $ do
      filePath <- L.fromNormalizedFilePath <$> L.uriToNormalizedFilePath uri
      let (wd, _) = splitFileName filePath
      Just wd

------------------------
-- Typechecking cache --
------------------------

cacheTypedProgram :: L.NormalizedUri -> VFS.VirtualFile ->
  TypeCheckingResult -> ServerM ()
cacheTypedProgram uri vfile program = do
  ref <- tcCache <$> ask
  liftIO $ modifyIORef ref $ Map.insert uri (version, program)
  where
    version = VFS.virtualFileVersion vfile

getCachedTypedProgram :: L.NormalizedUri -> VFS.VirtualFile
  -> ServerM (Maybe TypeCheckingResult)
getCachedTypedProgram uri vfile = do
  mcached <- (tcCache <$> ask) >>=
    (liftIO . readIORef) >>=
    (return . Map.lookup uri)
  case mcached of
    Just (version', program)
      | version == version' -> return $ Just program
    _ -> return Nothing
  where
    version = VFS.virtualFileVersion vfile

evictCachedTypedProgram :: L.NormalizedUri -> ServerM ()
evictCachedTypedProgram uri = do
  ref <- tcCache <$> ask
  liftIO $ modifyIORef ref $ Map.delete uri

typeCheck
  :: L.NormalizedUri
  -> VFS.VirtualFile
  -> Compiler.CmdOptions
  -> [Module (LProgram T.Text)]
  -> ServerM TypeCheckingResult
typeCheck uri vfile cmdOptions modules = do
  mcached <- getCachedTypedProgram uri vfile
  case mcached of
    Nothing -> do
      tcRes <- liftIO $ Compiler.typeCheck cmdOptions modules
      cacheTypedProgram uri vfile tcRes
      return tcRes
    Just tcRes ->
      return tcRes

typeCheckHandler :: L.NormalizedUri -> VirtualFile -> ServerM ()
typeCheckHandler uri vfile = L.withIndefiniteProgress (T.pack message) L.Cancellable runCheck
  where
    runCheck = do
      sendDiagnostics uri (virtualFileVersion vfile) []
      logDebug message
      emodules <- parse cmdOptions
      case emodules of
        Left err@(Compiler.ParseError loc msg) -> do
          logDebug $ show err
          let msg' = renderStrictText msg
          case locToRange loc of
            Just range ->
              sendDiagnostics uri
                (virtualFileVersion vfile)
                [ diagError range msg' ]
            Nothing ->
              sendNotification msg'

        Right modules -> do
          logDebug $ printf "Typechecking file '%s'" filePath
          tcRes <- typeCheck uri vfile cmdOptions modules
          let msgList = getSortedMsgs (tcRes ^. messages)
          mapM_ (logDebug . render . prettyMessage) msgList

          let notsAndDiags = map (messageToLSP fileName) msgList
          let nots = concatMap fst notsAndDiags
          let diags = concatMap snd notsAndDiags

          case nots of
            (_ : _) -> sendNotification $ T.unlines nots
            _ -> return ()

          -- It is important to always send diagnostics. If there were no errors
          -- an empty diagnostics list clears previous errors.
          sendDiagnostics uri (virtualFileVersion vfile) diags
    message = printf "Parsing file '%s'" filePath
    L.NormalizedUri _ filePath = uri
    cmdOptions = getCmdOptions uri
    fileName = Compiler._input cmdOptions

withVirtualFile
  :: L.NormalizedUri
  -> (VirtualFile -> ServerM ())
  -> ServerM ()
withVirtualFile uri act = do
  mdoc <- L.getVirtualFile uri
  case mdoc of
    Just file -> do
      logDebug $ "Found virtual file: " ++ show uri
      act file
    Nothing ->
      logDebug $ "Didn't find file in the VFS: " ++ show uri

checkFile :: L.NormalizedUri -> ServerM ()
checkFile uri = withVirtualFile uri $ typeCheckHandler uri

-- +1 is necessary because ZK-SecreC position numbering starts from 1
variableEndPos :: FilePath -> Rope.Rope -> Int -> Int -> Maybe Position
variableEndPos fileName rope line character =
  case tokenEndPos line character lineText of
    Nothing -> Nothing
    Just end ->
      Just $ Position
      { _posFilename = fileName
      , _posLine = _posLine end + 1
      , _posCol = _posCol end + 1
      }
  where
    pos = Rope.rowColumnCodeUnits (Rope.RowColumn line character) rope
    lineText = Rope.toText $ Rope.takeWhile (/= '\n') $
      snd $ Rope.splitAt pos rope

gotoDefinition
  :: L.Uri
  -> L.Position
  -> ( Either L.ResponseError (L.ResponseResult 'L.TextDocumentDefinition)
       -> ServerM () )
  -> ServerM ()
gotoDefinition uri position responder =
  withVirtualFile normalizedUri $ \vfile -> do

  eLoc <- runExceptT $ do
    lift $ logDebug $ printf "Parsing file '%s'" filePath
    emodules <- lift $ parse cmdOptions
    modules <- either (const $ throwE "Parsing failed") return emodules

    lift $ logDebug $ printf "Typechecking file '%s'" filePath
    tcRes <- lift $ typeCheck normalizedUri vfile cmdOptions modules
    program <- maybe (throwE "Typechecking failed") return
      (tcRes ^. typedProgram)

    let index = indexProgram program
    let zkscPos = variableEndPos
          (takeFileName $ T.unpack filePath)
          (VFS._text vfile)
          (position ^. L.line)
          (position ^. L.character)
    let maybeRange = do
          pos <- zkscPos
          sym <- symbolLookup pos index
          locToRange $ _definition sym
    range <- maybe (throwE "Could not find symbol") return maybeRange
    return $ L.Location
      { L._uri = uri
      , L._range = range
      }

  case eLoc of
    Left err -> do
      logDebug err
      responder $ Right $ L.InR $ L.InL $ L.List []
    Right loc ->
      responder $ Right $ L.InL loc

  where
    normalizedUri = L.toNormalizedUri uri
    L.NormalizedUri _ filePath = normalizedUri
    cmdOptions = getCmdOptions normalizedUri

lspHandlers :: TChan ReactorInput -> ServerEnv -> L.Handlers ServerM
lspHandlers rin logEnv = L.mapHandlers goReq goNot handle
  where
    goReq :: forall (a :: L.Method 'L.FromClient 'L.Request).
      L.Handler ServerM a -> L.Handler ServerM a
    goReq f = \msg k -> do
      lspEnv <- L.getLspEnv
      liftIO $ atomically $ writeTChan rin $
        ReactorAction $ runServerM lspEnv $ f msg k

    goNot :: forall (a :: L.Method 'L.FromClient 'L.Notification).
      L.Handler ServerM a -> L.Handler ServerM a
    goNot f = \msg -> do
      lspEnv <- L.getLspEnv
      liftIO $ atomically $ writeTChan rin $
        ReactorAction $ runServerM lspEnv $ f msg

    runServerM lspEnv act =
      L.runLspT lspEnv $ runReaderT (unServerM act) logEnv

handle :: L.Handlers ServerM
handle = mconcat
  [ notificationHandler L.SInitialized $ const $ return ()

  , notificationHandler L.STextDocumentDidOpen $ \msg -> do
    let doc  = msg ^. L.params . L.textDocument . L.uri
        fileName =  L.uriToFilePath doc
    logDebug $ "Processing TextDocumentDidOpen for: " ++ show fileName
    checkFile $ L.toNormalizedUri doc

  , notificationHandler L.STextDocumentDidChange $ \msg -> do
    let doc  = msg ^. L.params
                    . L.textDocument
                    . L.uri
                    . to L.toNormalizedUri
    logDebug $ "Processing TextDocumentDidChange for: " ++ show doc
    checkFile doc

  , notificationHandler L.STextDocumentDidSave $ \msg -> do
    let doc = msg ^. L.params . L.textDocument . L.uri
        fileName = L.uriToFilePath doc
    logDebug $ "Processing TextDocumentDidSave for: " ++ show fileName
    checkFile $ L.toNormalizedUri doc

  , notificationHandler L.STextDocumentDidClose $ \msg -> do
    let doc = msg ^. L.params . L.textDocument . L.uri
        fileName = L.uriToFilePath doc
    logDebug $ "Processing TextDocumentDidClose for: " ++ show fileName
    evictCachedTypedProgram $ L.toNormalizedUri doc

  , notificationHandler L.SWorkspaceDidChangeWatchedFiles $ const $ return ()

  , requestHandler L.STextDocumentDefinition $ \req responder -> do
    let doc = req ^. L.params . L.textDocument . L.uri
    let pos = req ^. L.params . L.position
    let fileName = L.uriToFilePath doc
    logDebug $ "Processing TextDocumentDefinition for: " ++ show fileName
    gotoDefinition doc pos responder
  ]

main :: IO ()
main = run =<< cmdArgs serverArgs
