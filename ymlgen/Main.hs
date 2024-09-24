{-# LANGUAGE ScopedTypeVariables #-}
module Main where


import Basic.Message
import Compiler
  ( CmdOptions (..)
  , defaultCmdOptions
  , parse
  , typeCheck
  , typedModules
  , messages
  , throw
  )
import qualified CSV
import Support.Pretty
import Version
import Typing.TcM (runTcM)
import Typing.Typing (TypedProgram(..), TypedTopExtern(_tExtIsPublic), TypedTopFunction(_tFunIsPublic))
import Yaml
import YamlGen

import Control.Exception (Handler (..), catches)
import Control.Lens ((^.))
import Data.Foldable (for_)
import Data.Graph
import System.Console.CmdArgs
import System.Environment
import System.Exit (die)
import System.FilePath
import System.IO


descriptionDir
  :: FilePath
descriptionDir
  = "ymlgen" </> "Description"

debugGroup :: Ann
debugGroup = groupname "Debug options"

cmdOptions :: CmdOptions
cmdOptions = defaultCmdOptions
  { _input = def &= argPos 0
                 &= typFile
  , _librarySearchPaths = def &= help "Library search path."
                              &= name "library-path"
                              &= name "L"
                              &= explicit
                              &= typFile

  -- debug
  , _debug = def &= help "Debug output during ZK-SecreC $pre computations."
                 &= name "debug"
                 &= explicit
                 &= debugGroup
  , _debugPrintEffectTypes = def &= help "Print derived effect types."
                                 &= name "debug-print-effect-types"
                                 &= explicit
                                 &= debugGroup
  , _debugPrintAst = def &= help "Print abstract syntax tree."
                         &= debugGroup
                         &= name "debug-print-ast"
                         &= explicit
  , _debugPrintRenamedAst = def &= help "Print renamed abstract syntax tree."
                                &= debugGroup
                                &= name "debug-print-renamed-ast"
                                &= explicit
  , _debugPrintTypedAst = def &= help "Print type checked abstract syntax tree."
                              &= debugGroup
                              &= name "debug-print-typed-ast"
                              &= explicit
  , _verbose = def &= help "Report various information messages."
                   &= name "verbose"
                   &= explicit
  }
  &= summary ("ZK-SecreC compiler " ++ version)
  &= program "ymlgen"

catchExceptions :: IO a -> IO a
catchExceptions action =
  action `catches` [ Handler (\(e :: Messages) -> die $ show e) ]

readDescrMap
  :: FilePath -> IO (FilePath , DescrMap)
readDescrMap name
  = do
      let outputFile = name <.> "yaml"
      let inputFile = descriptionDir </> name <.> "csv"
      descrmap <- CSV.parse <$> readFile inputFile
      return (outputFile , descrmap)

writeYamlDoc
  :: YamlVal -> FilePath -> IO ()
writeYamlDoc yaml file
  = do
      h <- openFile file WriteMode
      hPutStrLn h "---"
      hPutStrLn h (prettys 0 False yaml "...")
      hClose h

mainInput :: CmdOptions -> IO ()
mainInput options = catchExceptions $ do
  modules <- either (die . show) return =<< parse options

  tcRes <- typeCheck options modules

  for_ (getSortedMsgs (tcRes ^. messages)) $ \msg -> do
    hPutStrLn stderr $ render $ prettyMessage msg
  
  let mTypedModules = tcRes ^. typedModules
  case mTypedModules of
    Just typedModules
      -> do
           let (prog , name , _) = last typedModules
           let moduleName = dropExtension name
           (outputFile , descrmap) <- readDescrMap moduleName
           let docfuns = fmap externToDocFun (filter _tExtIsPublic (_tProgExterns prog)) ++ fmap functionToDocFun (filter _tFunIsPublic (flattenSCCs (_tProgFunctions prog)))
           let yaml = yamlGenModule moduleName descrmap docfuns
           writeYamlDoc yaml outputFile
    _ -> throw "Failed to type check program."


main
  :: IO ()
main
  = do
      args <- getArgs
      if null args -- generating docs for builtins
        then do
          let moduleName = "Builtin"
          (outputFile , descrmap) <- readDescrMap moduleName
          (yamlopt , _) <- runTcM (yamlGenBuiltin moduleName descrmap)
          case yamlopt of
            Just yaml
              -> writeYamlDoc yaml outputFile
            _ -> fail "Yaml could not be generated"
        else 
          mainInput =<< cmdArgs cmdOptions

