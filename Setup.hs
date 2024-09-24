{-# LANGUAGE CPP #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

import Data.List
import Data.Maybe (fromMaybe)
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import System.Exit (ExitCode(..))
import System.IO
import System.Process

{-
 - This is all taken from rmind source code
 -}

#if !(MIN_VERSION_Cabal(2,0,0))
versionNumbers :: Version -> [Int]
versionNumbers = versionBranch

mkFlagName :: String -> FlagName
mkFlagName = FlagName
#endif

#if !(MIN_VERSION_Cabal(2,1,0))
lookupFlagAssignment :: FlagName -> FlagAssignment -> Maybe Bool
lookupFlagAssignment = lookup
#endif

versionTmpl :: String
versionTmpl =
  intercalate "\n"
  [ "module Version (version) where"
  , "version :: String"
  , "version = \""
  ]

getCommit :: IO String
getCommit = do
  (_, Just out, _, p) <-
    createProcess (shell "git rev-parse --short HEAD") { std_out = CreatePipe }
  code <- waitForProcess p
  case code of
    ExitFailure _ -> return "dev"
    _ -> (("git " ++) . head_ . lines) <$> hGetContents out
  where
    head_ (x:_) = x
    head_ [] = ""

myConfHook :: (GenericPackageDescription, HookedBuildInfo) -> ConfigFlags -> IO LocalBuildInfo
myConfHook p@(gpdesc, _) cfg = do
  commit <- getCommit
  let
      mRelFlag = lookupFlagAssignment (mkFlagName "release") $ configConfigurationsFlags cfg
      release = fromMaybe False mRelFlag
      cabalVersion =
        intercalate "." $ map show $ versionNumbers $
        pkgVersion $ package $ packageDescription gpdesc
      version | release = cabalVersion
              | otherwise = concat [cabalVersion, " (", commit, ")"]
      mod = concat [versionTmpl, version, "\"\n"]
  writeFile "src/Version.hs" mod
  confHook simpleUserHooks p cfg

main :: IO ()
main =
  defaultMainWithHooks simpleUserHooks
  { confHook = myConfHook }