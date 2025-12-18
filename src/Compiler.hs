{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
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

module Compiler (
  -- CmdOptions with lenses
  CmdOptions (..),
  SourceFileHandle (..),
  defaultCmdOptions,
  input,
  librarySearchPaths,
  debug,
  debugPrintAst,
  debugPrintRenamedAst,
  debugPrintTypedAst,
  debugPrintCore,
  verbose,
  genBuiltinDoc,
  genModuleDoc,

  -- Compilation stages
  FileSystemM (..),
  runParser,
  parse,
  typeCheck,
  parseCCC,
  checkConfiguration,
  compile,

  -- Typechecking result record
  TypeCheckingResult (..),
  typedModules,
  typedProgram,
  messages,
  freeUnique,
  structEnv,
  synonymOccurs,
  builtins,

  -- Exception
  ParseError (..),
  prettyParseError,
  throw
) where

import Basic.Location (Location (NoLocation), Position (..), mkLocation, unLocated)
import Basic.Message (Message)
import qualified CCC.Parser
import CCC.Syntax
import Control.Lens ((^.))
import Control.Lens.TH (makeLenses)
import Control.Monad.IO.Class
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT, throwE)
import Core.LambdaLifting (coreLambdaLift)
import Core.Pretty (pprintCoreProgram)
import Core.Translate (programToCore, runTrM)
import qualified Data.ByteString as BS
import Data.Data (Data)
import Data.Graph (SCC(..), stronglyConnCompR)
import Data.IORef (readIORef)
import Data.List (find)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TextEncoding
import Data.Typeable (Typeable)
import Parser.Monad (ParseResult (..), ParseState (..), Parser, unParse)
import Control.Applicative ((<|>))
import Control.Monad (when, forM, foldM, unless)
import Parser.Precedence (reorderExprs)
import Parser.Syntax (Import (..), LProgram, Module, Program (..), TypeScheme)
import Parser.SyntaxDump (dumpLProgram, dumpProgram, dumpTypedProgram)
import Prelude hiding (readFile)
import qualified Parser.Monad
import qualified Parser.Parser
import Rust.CoreToRust (coreToRust)
import Support.Bag (Bag)
import Support.Pretty (Doc, colon, nest, pretty, render, vcat, ($$), (<+>))
import Support.UniqMap (UniqMap)
import Support.Unique (Unique)
import System.Directory (findFile)
import System.Environment (lookupEnv)
import System.FilePath (replaceExtension, splitFileName, (</>))
import Text.Printf (printf)
import Typing.Builtin (initBuiltins)
import Typing.Rename (rename)
import Typing.StructEnv (StructEnv)
import Typing.TcM
  ( runTcM,
    tcDebugPrint,
    tcMsgs,
    tcSetVerbose,
    tcStructEnv,
    tcSupply,
    tcWrapLoc,
    tcSynonymOccurs,
    tcDocBuiltins,
  )
import Typing.Typing (TypedProgram (..), TypedDefault(..), tcModules)
import Basic.Name
import Basic.Var
import EmbeddedStdlib
import Control.Monad.Trans.Maybe
import Typing.EffectChecker (ecModules)
import CompilerException
import ConfigurationCheck

data CmdOptions
  = CmdOptions
  { _input :: FilePath
  , _configuration :: Maybe FilePath
  , _outputPath :: Maybe String
  , _librarySearchPaths :: [FilePath]

  -- debug
  , _debug :: Bool
  , _debugPrintEffectTypes :: Bool
  , _debugPrintAst :: Bool
  , _debugPrintRenamedAst :: Bool
  , _debugPrintTypedAst :: Bool
  , _debugPrintCore :: Bool
  , _verbose :: Bool

  -- documentation
  , _genModuleDoc :: Bool
  , _genBuiltinDoc :: Bool
  } deriving (Show, Data, Typeable)

makeLenses ''CmdOptions

defaultCmdOptions :: CmdOptions
defaultCmdOptions
  = CmdOptions
  { _input = ""
  , _configuration = Nothing
  , _outputPath = Nothing
  , _librarySearchPaths = []
  , _debug = False
  , _debugPrintEffectTypes = False
  , _debugPrintAst = False
  , _debugPrintRenamedAst = False
  , _debugPrintTypedAst = False
  , _debugPrintCore = False
  , _verbose = False
  , _genModuleDoc = False
  , _genBuiltinDoc = False
  }

data SourceFileHandle
  = SourceOnDisk FilePath
  | SourceInMemory String BS.ByteString

sourceFileHandleName :: SourceFileHandle -> String
sourceFileHandleName = \case
  SourceOnDisk fp -> fp
  SourceInMemory name _ -> name

class MonadIO m => FileSystemM m where
  fsFindFile :: [FilePath] -> [FilePath] -> String -> m (Maybe SourceFileHandle)
  fsReadFile :: SourceFileHandle -> m T.Text
  fsReadFileByteString :: FilePath -> m BS.ByteString

instance FileSystemM IO where
  fsFindFile userPaths systemPaths fp = runMaybeT $
    onDisk (findFile userPaths fp) <|>
    inMemory (return (find (\(f, _) -> f == fp) embeddedStdlib)) <|>
    onDisk (findFile systemPaths fp)
    where
      onDisk act = SourceOnDisk <$> MaybeT act
      inMemory act = uncurry SourceInMemory <$> MaybeT act
  fsReadFile = \case
      SourceInMemory _ bs -> return $ TextEncoding.decodeUtf8 bs
      SourceOnDisk path -> TextEncoding.decodeUtf8 <$> BS.readFile path

  fsReadFileByteString = BS.readFile

getParserState :: FileSystemM m => SourceFileHandle -> ExceptT ParseError m ParseState
getParserState sourceFileHandle = do
  let pos = Position (sourceFileHandleName sourceFileHandle) 1 1
  inp <- lift $ fsReadFile sourceFileHandle
  return ParseState
    { _parsePosition = pos
    , _parseInput = inp
    , _parseLastLoc = mkLocation pos pos
    , _parsePrevChar = '\0'
    , _parseAlexState = [0]
    }

data ParseError = ParseError Location (Doc ())

prettyParseError :: ParseError -> Doc ()
prettyParseError (ParseError loc msg) = pretty loc <> colon <+> msg

throwParseError :: Monad m => Doc () -> ExceptT ParseError m a
throwParseError = throwE . ParseError NoLocation

instance Show ParseError where
  show = render . prettyParseError

runParser :: MonadIO m => ParseState -> Parser a -> ExceptT ParseError m a
runParser state parser =
  case unParse parser state of
    ParseOK _ x -> return x
    ParseFail err -> throwE $
      ParseError
      (Parser.Monad._parseErrorLocation err)
      (Parser.Monad._parseErrorMessage err)

parseModule :: FileSystemM m => [FilePath] -> [FilePath] -> FilePath
  -> [Module (LProgram T.Text)] -> ExceptT ParseError m [Module (LProgram T.Text)]
parseModule userSearchPaths systemSearchPaths file modules =
  case find (\(_, f, _) -> file == f) modules of
    Just _ -> return modules
    Nothing -> do
      mfile <- lift $ fsFindFile userSearchPaths systemSearchPaths file
      case mfile of
        Nothing -> throwParseError $ pretty (printf "File %s not found." file :: String)
        Just file' -> do
          parserState <- getParserState file'
          program <- runParser parserState Parser.Parser.parse
          let imports = map unLocated $ _programImports $
                unLocated program
          let fileNames = map repExt imports
          let modul = (program, file, fileNames)
          let modules' = modul : modules
          foldM (flip (parseModule userSearchPaths systemSearchPaths)) modules' fileNames
  where
    repExt i = replaceExtension (T.unpack $ _importName i) ".zksc"

reportCycle :: [Module a] -> Doc ann
reportCycle xs =
  nest 2 ("Cycle between" $$ nest 2 (vcat $ map pretty names))
  where
    names = map (\(_, x, _) -> x) xs

getHome :: IO (Maybe FilePath)
getHome = do
  mXdgHome <- lookupEnv "XDG_DATA_HOME"
  mHome <- lookupEnv "HOME"
  return $ (</> ".zksc") <$> (mXdgHome <|> mHome)

-- | Parse program based on given options.
-- Returned modules are topologically sorted.
parse
  :: FileSystemM m
  => CmdOptions
  -> m (Either ParseError [Module (LProgram T.Text)])
parse CmdOptions{..} = runExceptT $ do
  mHome <- liftIO getHome
  let userSearchPaths = baseDir : _librarySearchPaths
  let systemSearchPaths =
        maybe id (:) ((</> "stdlib") <$> mHome)
        ["/usr/lib/zksc/stdlib"]

  -- Parse modules
  -- NOTE: stronglyConnCompR orders modules by reverse topological order
  moduleSCC <- stronglyConnCompR <$> parseModule userSearchPaths systemSearchPaths fileName []

  -- Report errors about recursive imports:
  let cycles = [s | CyclicSCC s <- moduleSCC]
  unless (null cycles) $ do
    let docs = map reportCycle cycles
    throwParseError $ "Recursive imports found:" $$ vcat docs

  let modules = [v | AcyclicSCC v <- moduleSCC]
  when _debugPrintAst $ do
    let (program, _, _) = last modules
    liftIO $ putStrLn $ render $ dumpLProgram program

  return modules

  where
    (baseDir, fileName) = splitFileName _input

data TypeCheckingResult
  = TypeCheckingResult
  { _typedModules :: Maybe [Module TypedProgram]
  , _typedProgram :: Maybe TypedProgram
  , _messages :: Bag Message
  , _freeUnique :: Unique
  , _structEnv :: UniqMap StructEnv
  , _synonymOccurs :: UniqMap Location
  , _builtins :: [(T.Text, BuiltinInfo, TypeScheme TyVar)]
  }

makeLenses ''TypeCheckingResult

-- construct full program from main and imported modules
joinModules
  :: [Module TypedProgram] -> TypedProgram
joinModules typedModules
  = let
      progs = map (\(p, _, _) -> p) typedModules
      exts = concatMap _tProgExterns progs
      funs = concatMap _tProgFunctions progs
      impls = concatMap _tProgStructImpls progs
      defaults = TypedDefault (concatMap (_tDefaultFields . _tProgDefaults) progs)
    in
    TypedProgram
    { _tProgExterns = exts
    , _tProgFunctions = funs
    , _tProgStructImpls = impls
    , _tProgImports = []
    , _tProgDefaults = defaults
    , _tVars = []
    }

typeCheck :: CmdOptions -> [Module (LProgram T.Text)] -> IO TypeCheckingResult
typeCheck CmdOptions{..} modules = do
  let runTcM' = runTcM . tcSetVerbose _verbose . initBuiltins
  (mTypedModules, env) <- runTcM' $ do
    modules' <- forM modules $ \(p, name, imports) -> do
      p' <- tcWrapLoc reorderExprs p
      return (p', name, imports)

    -- NOTE: The fold reverses the order.
    renamedModules <- reverse <$> foldM rename [] modules'

    -- TODO: Should print all modules not only the main one. Same below.
    when _debugPrintRenamedAst $ do
      let (lprogram, _, _) = last renamedModules
      let program' = unLocated lprogram
      liftIO $ putStrLn $ render $ dumpProgram program'
    tcDebugPrint "\x1b[32mRenaming done\x1b[0m"

    typedModules <- tcModules renamedModules

    when _debugPrintTypedAst $ do
      let (program'', _, _) = last typedModules
      liftIO $ putStrLn $ render $ dumpTypedProgram program''
    tcDebugPrint "\x1b[32mTypeChecking done\x1b[0m"

    return typedModules

  messages' <- readIORef (env ^. tcMsgs)
  unique <- readIORef (env ^. tcSupply)
  structEnv' <- readIORef (env ^. tcStructEnv)
  synonymOccurs' <- readIORef (env ^. tcSynonymOccurs)
  builtins <- readIORef (env ^. tcDocBuiltins)

  let mTypedProgram = fmap joinModules mTypedModules
  (messages', unique) <- case mTypedProgram of
    Just typedProgram -> do
      res <- ecModules typedProgram _verbose _debugPrintEffectTypes unique structEnv'
      case res of
        Left msgs -> return (msgs <> messages', unique) -- mapM_ (putStrLn . render . prettyMessage) msgs
        Right unique' -> return (messages', unique')
    Nothing -> return (messages', unique)

  return TypeCheckingResult
    { _typedModules = mTypedModules
    , _typedProgram = mTypedProgram
    , _messages = messages'
    , _freeUnique = unique
    , _structEnv = structEnv'
    , _synonymOccurs = synonymOccurs'
    , _builtins = builtins
    }

parseCCC
  :: FileSystemM m
  => CmdOptions -> m (Either ParseError (CCC T.Text))
parseCCC CmdOptions{..} = runExceptT $ do
  let (baseDir, fileName) = splitFileName (fromMaybe ("cfg" </> "permitall.ccc") _configuration)
  mfile <- lift $ fsFindFile [baseDir] [] fileName
  case mfile of
    Nothing -> throwParseError $ pretty (printf "File %s not found." fileName :: String)
    Just file -> do
      parserState <- getParserState file
      runParser parserState CCC.Parser.parse

compile :: FileSystemM m => CmdOptions -> Maybe TypedProgram -> Unique -> UniqMap StructEnv -> CCC T.Text -> m ()
compile CmdOptions{..} mTypedProgram uniq senv ccc = do
  typedProgram <- case mTypedProgram of
    Nothing -> throw "Failed to type check program."
    Just res -> return res
  testdata <- checkConfiguration typedProgram ccc
  if _verbose
    then do
      liftIO . putStrLn . render $ "Supported rings:"
      liftIO . putStrLn . render $ vcat (fmap pretty (_supportedRings testdata))
      liftIO . putStrLn . render $ "Supported challenges:"
      liftIO . putStrLn . render $ vcat (fmap pretty (_supportedChallenges testdata))
      liftIO . putStrLn . render $ "Supported conversions:"
      liftIO . putStrLn . render $ vcat (fmap pretty (_supportedConverts testdata))
      liftIO . putStrLn . render $ "Supported plugins:"
      liftIO . putStrLn . render $ vcat (fmap pretty (_supportedPlugins testdata))
    else return ()
  case runTrM uniq senv (programToCore typedProgram) of
    Left err -> throw $ "Failed to translate to core: " ++ err
    Right (coreProgram, uniq') -> liftIO $ do
      let coreProgram1 = fst $ coreLambdaLift uniq' coreProgram
      when _debugPrintCore $
        putStrLn $ render $ pprintCoreProgram coreProgram1
      coreToRust senv _outputPath testdata coreProgram1

