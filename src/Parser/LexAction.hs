{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Parser.LexAction
  ( Action, liftAction, mapAction,
    skip, tokSimple, tokText, tokChar, tokInteger, tokError,
    enterState, enterState', exitState, exitState'
  )
  where

import Basic.Location
import Parser.Monad
import Support.Pretty

import Data.Char (digitToInt)
import qualified Data.Text as Text

type Action a = Location -> Text.Text -> Int -> Parser a

mapAction :: (a -> b) -> Action a -> Action b
mapAction f act loc txt len = f `fmap` act loc txt len

-- | Lift a parsing action to a lexer action.
liftAction :: Parser a -> Action a
liftAction m _loc _buf _len = m

skip :: Int -> Action a -> Action a
skip k act loc txt len
    | k >= 0 && k <= len = act loc (Text.drop k txt) (len - k)
    | otherwise = fail "Internal error in function \"Parser.Lexer.skip\"."

tokSimple :: a -> Action (Located a)
tokSimple tok loc _buf _len = return $ Located loc tok

tokError :: String -> Action a
tokError msg loc _buf _len = parseError loc (pretty msg)

tokText :: Action (Located Text.Text)
tokText loc buf len = return $ Located loc (Text.take len buf)

tokChar :: Action (Located Char)
tokChar loc buf _ = return $ Located loc (Text.head buf)

tokInteger :: Num a => a -> Action (Located a)
tokInteger base loc buf len = tokSimple value loc buf len
    where
        digits = Text.take len buf
        value = Text.foldl' step 0 digits
        step acc c = acc * base + fromIntegral (digitToInt c)

enterState' :: AlexState -> Action a -> Action a
enterState' st act loc buf len = pushParseAlexState st >> act loc buf len

enterState :: AlexState -> Parser a -> Action a
enterState st = enterState' st . liftAction

exitState :: Parser a -> Action a
exitState = exitState' . liftAction

exitState' :: Action a -> Action a
exitState' act loc buf len = popParseAlexState >> act loc buf len
