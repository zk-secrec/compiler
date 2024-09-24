{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module RegressionFiles where

import Control.Monad
import Data.List (isPrefixOf)
import qualified Data.Text as T
import System.Directory
import System.FilePath
import Test.HUnit (assertFailure)

import Basic.Message
import Compiler
import SpecHelper
import Support.Bag
import Support.Pretty

regressionFiles :: Spec
regressionFiles =
  describe "regression tests:" $ do
    let dir = "test/regression" :: FilePath
    files <- runIO $ getDirectoryContents dir
    let fil path = ("zksc" `isExtensionOf` path) &&
          ("example" `isPrefixOf` takeFileName path)
    let files' = ((dir <> "/") <>) <$> filter fil files
    let modMap = mempty
    let mod = 251
    forM_ files' $ \path -> it (path <> " compiles successfully") $ do
      let opt = defaultCmdOptions
            & input .~ path
            & modulus .~ [T.pack $ show mod]
      modules <- either (error . show) return =<< parse opt
      tcRes <- Compiler.typeCheck opt modMap modules
      let prog = tcRes ^. typedProgram
      case prog of
        Nothing -> assertFailure . unlines . toListBag $
          render . prettyMessage <$> (tcRes ^. messages)
        Just _  -> return ()
      compile opt mod modMap prog (tcRes ^. freeUnique) (tcRes ^. structEnv)
