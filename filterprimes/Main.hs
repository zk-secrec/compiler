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


import Control.Monad.Except
import Data.Char
import Data.List
import qualified Data.Text as T
import System.Environment
import System.IO

import Support.Pretty
import Basic.Location
import Parser.Monad hiding (prettyParseError)
import CCC.Parser
import CCC.Syntax
import ConfigurationCheck
import Compiler


trim
  :: String -> String
trim
  = dropWhileEnd isSpace . dropWhile isSpace

readPrimes
  :: String -> [Integer]
readPrimes
  = fmap (read . trim) . lines

isSupportedBy
  :: Integer -> [Located (CCCType T.Text)] -> Bool
isSupportedBy n
  = not . null . unLocated . fieldIxs (noLoc n)

shift
  :: String -> String
shift
  = (replicate 4 ' ' ++)

getParserState
  :: FilePath -> IO ParseState
getParserState file
  = let
      pos
        = Position file 1 1
    in
    do
      conts <- readFile file
      return $ ParseState
        { _parsePosition = pos
        , _parseInput = T.pack conts
        , _parseLastLoc = mkLocation pos pos
        , _parsePrevChar = '\0'
        , _parseAlexState = [0]
        }

main
  :: IO ()
main
  = do
      args@ ~[primefile, cccfile] <- getArgs
      if length args == 2
        then 
          do
            primeconts <- readPrimes <$> readFile primefile
            parserState <- getParserState cccfile
            cccconts <- runExceptT $ runParser parserState CCC.Parser.parse
            case cccconts of
              Right cccconts
                -> mapM_ print . filter (`isSupportedBy` _cccTypes cccconts) $ primeconts
              Left err
                -> hPutStr stderr . render $ prettyParseError err
        else 
          hPutStr stderr . unlines $
          [ "Usage: FilterPrimes <primefile> <cccfile>"
          , "where:"
          , shift "<primefile> contains all primes we support, one per line;"
          , shift "<cccfile> contains TA2 requirements in ccc format like described in Sect. 6 of the Circuit-IR specification."
          ]

