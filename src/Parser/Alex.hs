{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

{-# LANGUAGE BangPatterns #-}

module Parser.Alex (AlexInput (..), alexInputPrevChar, alexGetChar, alexGetByte, fixInput)
    where

import Basic.Location

import Data.Char
import Data.Word (Word8)
import qualified Data.Text as Text

data AlexInput = AlexInput {
        _alexPos      :: Position,
        _alexPrevChar :: {-# UNPACK #-} !Char,
        _alexInput    :: {-# UNPACK #-} !Text.Text
    }

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = _alexPrevChar

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte !input = case input of
  AlexInput pos _ txt -> case Text.uncons txt of
    Just (c, cs') -> let
        b  = fromIntegral $ ord $ adj c
        p' = movePos pos c
        i  = AlexInput p' c cs'
      in c `seq` i `seq` Just (b, i)
    Nothing -> Nothing

alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar input = getC <$> Text.uncons (_alexInput input)
    where
        getC (c, cs') = let
                p' = movePos (_alexPos input) c
            in p' `seq` cs' `seq` (c, AlexInput p' c cs')

fixInput :: AlexInput -> AlexInput -> Int -> AlexInput
fixInput input input' len =
    case Text.uncons $ Text.drop (len - 1) $ _alexInput input of
        Nothing -> input' { _alexInput = Text.empty }
        Just (c, cs') -> input' {
                _alexInput = cs',
                _alexPrevChar = c
            }

-- Force the unicode character to fit a single byte.
-- The following code is directly from GHC.
adj :: Char -> Char
adj c
    | c <= '\x06' = non_graphic
    | c <= '\x7f' = c
    | otherwise = case generalCategory c of
          UppercaseLetter       -> upper
          LowercaseLetter       -> lower
          TitlecaseLetter       -> upper
          ModifierLetter        -> other_graphic
          OtherLetter           -> lower
          NonSpacingMark        -> other_graphic
          SpacingCombiningMark  -> other_graphic
          EnclosingMark         -> other_graphic
          DecimalNumber         -> digit
          LetterNumber          -> other_graphic
          OtherNumber           -> digit
          ConnectorPunctuation  -> symbol
          DashPunctuation       -> symbol
          OpenPunctuation       -> other_graphic
          ClosePunctuation      -> other_graphic
          InitialQuote          -> other_graphic
          FinalQuote            -> other_graphic
          OtherPunctuation      -> symbol
          MathSymbol            -> symbol
          CurrencySymbol        -> symbol
          ModifierSymbol        -> symbol
          OtherSymbol           -> symbol
          Space                 -> space
          _other                -> non_graphic
    where
        non_graphic     = '\x0'
        upper           = '\x1'
        lower           = '\x2'
        digit           = '\x3'
        symbol          = '\x4'
        space           = '\x5'
        other_graphic   = '\x6'
