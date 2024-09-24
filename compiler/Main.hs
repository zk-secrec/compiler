{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-cse #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Main where

import Basic.Message
import CCC.Checks (checkCCCSoundness)
import Compiler
  ( CmdOptions (..)
  , parse
  , typeCheck
  , parseCCC
  , compile
  , typedProgram
  , messages
  , freeUnique
  , structEnv
  , builtins
  )
import Support.Pretty
import Version

import Control.Exception (Handler (..), catches)
import Control.Lens ((^.))
import Control.Monad
import Data.Foldable (for_)
import System.Console.CmdArgs
import System.Exit (die)
import System.IO (hPutStrLn, stderr)
import qualified DocGen as Doc


debugGroup :: Ann
debugGroup = groupname "Debug options"

outputHelp :: String
outputHelp = "Output path. In --text mode either the prefix of the three files or \"-\" for stdout. In --binary mode either a directory for the three files, path of a single concatenated .sieve file or \"-\" for stdout."

cmdOptions :: CmdOptions
cmdOptions = CmdOptions
  { _input = def &= argPos 0
                 &= typFile
  , _configuration = def &= help "CCC input file."
                         &= name "cfg"
                         &= name "c"
                         &= explicit
                         &= typFile
  , _outputPath = def &= help outputHelp
                      &= name "output"
                      &= name "o"
                      &= explicit
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
  , _debugPrintCore = def &= help "Print program in core form."
                          &= debugGroup
                          &= name "debug-print-core"
                          &= explicit
  , _verbose = def &= help "Report various information messages."
                   &= name "verbose"
                   &= explicit
  , _genModuleDoc = def &= help "Generate a YAML structure about the module"
                        &= name "generate-module-doc"
                        &= explicit
  , _genBuiltinDoc = def &= help "Generate a YAML structure about built-in functions"
                         &= name "generate-builtin-doc"
                         &= explicit
  }
  &= summary ("ZK-SecreC compiler " ++ version)
  &= program "zkscc"

catchExceptions :: IO a -> IO a
catchExceptions action =
  action `catches` [ Handler (\(e :: Messages) -> die $ show e) ]

mainInput :: CmdOptions -> IO ()
mainInput options@CmdOptions{..} = catchExceptions $ do
  modules <- either (die . show) return =<< parse options

  when _genModuleDoc $
    Doc.generateModuleYAML (last modules)

  tcRes <- typeCheck options modules

  when _genBuiltinDoc $
    Doc.generateBuiltinYAML (tcRes ^. builtins)

  for_ (getSortedMsgs (tcRes ^. messages)) $ \msg -> do
    hPutStrLn stderr $ render $ prettyMessage msg
  
  ccc <- either (die . show) return =<< parseCCC options
  checkCCCSoundness ccc

  compile options (tcRes ^. typedProgram) (tcRes ^. freeUnique) (tcRes ^. structEnv) ccc

main :: IO ()
main =
  mainInput =<< cmdArgs cmdOptions
