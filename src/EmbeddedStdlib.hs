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

module EmbeddedStdlib (embeddedStdlib, embeddedCircuits) where

import qualified Codec.Compression.GZip as GZip
import qualified Data.ByteString.Lazy as LazyB
import qualified Data.ByteString as B
import Support.EmbedCompressedFiles
import System.FilePath.Find
import System.FilePath.Glob
import Language.Haskell.TH.Syntax
import Control.Arrow
import System.FilePath

{-
 - Here we embed stdlib/ and ciruitcs/ into the compiled library.
 - Both standard library and circuits are compressed.
 - TODO: This could cause issues with cabal, we should maybe use Paths_<pkg> to fix those.
 -}

embeddedCompressedStdlib :: [(FilePath, B.ByteString)]
embeddedCompressedStdlib = $(do
  filePaths <- runIO (find always (extension ==? ".zksc") "stdlib/")
  embedCompressedFiles filePaths)

embeddedCompressedCircuits :: [(FilePath, B.ByteString)]
embeddedCompressedCircuits = $(do
  filePaths <- runIO (namesMatching "circuits/*.txt")
  embedCompressedFiles filePaths)

dropPrefix :: FilePath -> FilePath
dropPrefix = snd . splitFileName

decompress :: B.ByteString -> B.ByteString
decompress = LazyB.toStrict . GZip.decompress . LazyB.fromStrict

embeddedStdlib :: [(FilePath, B.ByteString)]
embeddedStdlib = map (dropPrefix *** decompress) embeddedCompressedStdlib

embeddedCircuits :: [(FilePath, B.ByteString)]
embeddedCircuits = map (dropPrefix *** decompress) embeddedCompressedCircuits