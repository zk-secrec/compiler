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

module Support.EmbedCompressedFiles (embedCompressedFiles) where

import qualified Codec.Compression.GZip as GZip
import qualified Data.ByteString.Lazy as LazyB
import qualified Data.ByteString as B
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (qAddDependentFile)
import Data.FileEmbed
import Control.Monad

ebmedCompressedFile :: FilePath -> Q B.ByteString
ebmedCompressedFile path = do
  qAddDependentFile path
  compressedFile <- runIO $! GZip.compress <$> LazyB.readFile path
  return $! LazyB.toStrict compressedFile

pairToExp :: FilePath -> B.ByteString -> Q Exp
pairToExp path bs = do
  exp' <- bsToExp bs
  return $! TupE $! map Just [LitE $! StringL path, exp']

embedCompressedFiles :: [FilePath] -> Q Exp
embedCompressedFiles paths = do
  bs <- mapM ebmedCompressedFile paths
  ex <- zipWithM pairToExp paths bs
  SigE (ListE ex) <$> [t| [(FilePath, B.ByteString)] |]