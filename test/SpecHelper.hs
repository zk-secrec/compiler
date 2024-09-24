{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module SpecHelper (
  module Test.Hspec,
  module Text.RawString.QQ,

  -- parameters
  Parameters(..),
  def,
  witness,
  instance_,
  public,
  defaultModulus,
  optimize,

  -- lens
  module Control.Lens,

  -- assertions
  parses,
  typeChecks,
  compiles,
  compilesWith,
  compileFails,
  typeShouldBe,

  -- other useful functions
  typeCheck,
  findFunction
) where

import Control.Exception (catch)
import Control.Lens
import Control.Monad (unless, void)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader.Class (MonadReader, ask)
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Data.Bifunctor (second)
import Data.Foldable (find)
import Data.Graph (flattenSCCs)
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TextEncoding
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.HUnit (assertFailure)
import Test.Hspec
import Text.Printf (printf)
import Text.RawString.QQ (r, rQ)
import Text.Regex.TDFA ((=~))

import Basic.Location
import Basic.Message (getSortedMsgs, prettyMessage)
import Basic.Name (nameOccName)
import Basic.Var (varName)
import Compiler hiding (parse, typeCheck, compile)
import qualified Compiler
import Parser.Syntax (Type, Module, LProgram)
import Support.Pretty (Doc, Pretty(pretty), render)
import Support.Unique
import Support.UniqMap (UniqMap)
import Typing.StructEnv (StructEnv)
import Typing.Typing


type VFS = Map.Map FilePath T.Text

newtype TestM a
  = TestM { unTestM :: ReaderT VFS IO a }
  deriving (Applicative, Functor, Monad, MonadIO, MonadReader VFS)

runTestM :: TestM a -> VFS -> IO a
runTestM = runReaderT . unTestM

instance FileSystemM TestM where
  fsFindFile _ fileName = do
    vfs <- ask
    return $ case Map.lookup fileName vfs of
      Just _ -> Just fileName
      Nothing -> Nothing

  fsReadFile fileName = do
    vfs <- ask
    case Map.lookup fileName vfs of
      Just contents -> return contents
      Nothing -> throw $ printf "File %s not found." fileName

  fsReadFileByteString fileName =
    TextEncoding.encodeUtf8 <$> fsReadFile fileName

cmdOptions :: CmdOptions
cmdOptions =
  defaultCmdOptions
    & input .~ "inline"
    & instancePath ?~ "instance"
    & publicPath ?~ "public"
    & witnessPath ?~ "witness"
    & textOutput .~ True

renderPretty :: Pretty a => a -> String
renderPretty x = render (pretty x :: Doc ())

parse :: String -> IO [Module (LProgram T.Text)]
parse inp =
  either (throw . show) return =<<
  runTestM
  (Compiler.parse cmdOptions)
  (Map.singleton "inline" (T.pack inp))

typeCheck' :: String -> IO (TypedProgram, Unique, UniqMap StructEnv)
typeCheck' input = do
  tcRes <- Compiler.typeCheck cmdOptions Map.empty =<< parse input
  case tcRes ^. typedProgram of
    Nothing ->
      throw $ intercalate "\n" $
      map (render . prettyMessage) $
      getSortedMsgs $ tcRes ^. messages
    Just program ->
      return (program, tcRes ^. freeUnique, tcRes ^. structEnv)

typeCheck :: String -> IO TypedProgram
typeCheck inp = typeCheck' inp <&> (^. _1)

data Parameters
  = Parameters
  { _instance_ :: String
  , _witness :: String
  , _public :: Maybe String
  , _defaultModulus :: Integer
  , _optimize :: Bool
  }

makeLenses ''Parameters

def :: Parameters
def = Parameters
  { _instance_ = "{}"
  , _witness = "{}"
  , _public = Nothing
  , _defaultModulus = 1030307
  , _optimize = True
  }

compile :: Parameters -> String -> IO ()
compile Parameters{..} input = do
  (typedProgram, uniq, structEnv) <- typeCheck' input

  withSystemTempDirectory "zkscc-test-output-" $ \tmpDir ->
    let cmdOptions' = cmdOptions & outputPath ?~ (tmpDir </> "program") in
    runTestM
     (Compiler.compile cmdOptions' _defaultModulus modulusMap
       (Just typedProgram) uniq structEnv)
     (Map.fromList $ map (second T.pack)
      [ ("inline", input)
      , ("witness", _witness)
      , ("instance", _instance_)
      , ("public", fromMaybe "{}" _public)
      ])

  where
    modulusMap = Map.empty

findFunction :: T.Text -> TypedProgram -> Maybe TypedTopFunction
findFunction fn program =
  find (\f -> nameOccName (varName $ _tFunName f) == fn) $
  flattenSCCs $ _tProgFunctions program

typesEq :: Eq a => Type a -> Type a -> Bool
typesEq a b = f a == f b
  where
    f = transform stripLocation

parses :: String -> Expectation
parses inp = void (parse inp) `catch` handler
  where
    handler :: Compiler.CompilerException -> IO ()
    handler = assertFailure . show

typeChecks :: String -> Expectation
typeChecks inp = void $ typeCheck inp

compilesWith :: Parameters -> String -> Expectation
compilesWith = compile

compiles :: String -> Expectation
compiles = compilesWith def

compileFails :: String -> String -> Expectation
compileFails inp failPattern =
  (do compilesWith def inp
      assertFailure "Compilation did not fail.")
  `catch`
  (\(e :: CompilerException) -> do
      let msg = show e
      unless (msg =~ failPattern) $
        assertFailure $ printf "Exception:\n\"%s\"\ndoes not match regular expression \"%s\"" msg failPattern)

typeShouldBe :: (Eq a, Pretty a) => Type a -> Type a -> Expectation
typeShouldBe ty expected
  | typesEq ty expected = return ()
  | otherwise =
    assertFailure $ printf "Expected type '%s', got '%s'." (r ty) (r expected)
  where
    r = renderPretty
