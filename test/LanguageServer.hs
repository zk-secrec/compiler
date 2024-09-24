{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module LanguageServer (languageServer) where

import Control.Lens ((^.))
import Control.Monad (void)
import Control.Monad.IO.Class (liftIO)
import Data.Default (def)
import qualified Data.Text as T
import Language.LSP.Test
import Language.LSP.Types
import Language.LSP.Types.Lens
import Test.HUnit
import Test.Hspec hiding (it)
import qualified Test.Hspec
import Text.RawString.QQ


lspSession :: Session () -> IO ()
lspSession =
  runSessionWithConfig config serverCmd fullCaps dataDir
  where
    -- Change logging if something is bork and you want to see what's going on
    config = def { logStdErr = False
                 , logMessages = False
                 }
    serverCmd = "stack exec zksc-language-server -- --debug"
    dataDir = "/tmp"

createProgram :: T.Text -> Session TextDocumentIdentifier
createProgram = createDoc "program.zksc" "zk-secrec"

assertRange :: Position -> Position -> Range -> IO ()
assertRange expectedStart expectedEnd Range{..} = do
  assertEqual "start position" expectedStart _start
  assertEqual "end position" expectedEnd _end

assertMessage :: T.Text -> T.Text -> IO ()
assertMessage = assertEqual "message"

it :: HasCallStack => String -> Session () -> SpecWith ()
it description behavior = Test.Hspec.it description $ lspSession behavior

assertFindsDefinition
  :: TextDocumentIdentifier -> Position -> Range -> Session ()
assertFindsDefinition doc queryPos expectedDefRange = do
  resMsg <- request STextDocumentDefinition $ DefinitionParams
    { _textDocument = doc
    , _position = queryPos
    , _workDoneToken = Nothing
    , _partialResultToken = Nothing
    }
  liftIO $ case resMsg ^. result of
    Right (InL loc) ->
      assertEqual "definition position" expectedDefRange (loc ^. range)
    _ ->
      assertFailure "definition not found"

languageServer :: Spec
languageServer =
  describe "language server protocol:" $ do
    it "parse errors are reported as diagnostics" $ do
      doc <- createProgram "fn main() {}"

      -- No issues after opening the program
      diags <- waitForDiagnostics
      liftIO $ assertEqual "initial diagnostics list" [] diags

      -- Break the program by editing
      changeDoc doc [
        TextDocumentContentChangeEvent
        (Just (Range (Position 0 2) (Position 0 3)))
        Nothing
        ""
        ]

      diags <- waitForDiagnostics

      liftIO $ do
        assertEqual "number of diagnostics" 1 (length diags)
        let Diagnostic{..} = head diags
        let Range{..} = _range
        assertRange (Position 0 0) (Position 0 6) _range
        assertMessage "Parse error." _message

    it "type errors are reported as diagnostics" $ do
      void $ createProgram [r|
        fn main() {
          let x: bool $pre @prover = true;
          assert(x);
        } |]

      diags <- waitForDiagnostics

      liftIO $ do
        assertEqual "number of diagnostics" 1 (length diags)
        let Diagnostic{..} = head diags
        let Range{..} = _range
        assertRange (Position 3 17) (Position 3 18) _range
        assertMessage "Unsolved constraints: $post ~ $pre" _message

    it "goto definition finds variable declaration" $ do
      doc <- createProgram [r|
        fn main() {
          let x: uint $pre @public = 1;
          x;
        } |]

      -- No issues after opening the program
      void waitForDiagnostics

      -- Find x in 'x;'
      assertFindsDefinition doc (Position 3 10)
        (Range (Position 2 14) (Position 2 15))

    it "goto definition finds function definition" $ do
      doc <- createProgram [r|
        fn foo() {}
        fn main() {
          foo();
        } |]

      -- No issues after opening the program
      void waitForDiagnostics

      -- Find f in 'foo();'
      assertFindsDefinition doc (Position 3 10)
        (Range (Position 1 11) (Position 1 14))
