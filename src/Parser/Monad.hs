{-# LANGUAGE MultiParamTypeClasses #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Parser.Monad
    (Parser(..), ParseState(..), ParseResult(..), ParseError(..), AlexState,
     getParsePosition, getParseLocation,
     setParseLocation, setLexInput, getLexInput, returnEOF,
     popParseAlexState, topParseAlexState, pushParseAlexState, parseError,
     prettyParseError)
    where

import Basic.Location
import Parser.Alex
import Parser.HasEOF
import Support.Pretty

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Text as Text
import qualified Control.Monad.Fail as Fail

{- Data types: -}

newtype Parser a = Parser {
        unParse :: ParseState -> ParseResult a
    }

data ParseState = ParseState {
        _parsePosition     :: Position,
        _parsePrevChar     :: {-# UNPACK #-} !Char,
        _parseInput        :: {-# UNPACK #-} !Text.Text,
        _parseLastLoc      :: Location,
        _parseAlexState    :: [AlexState]
    }

type AlexState = Int

data ParseResult a
    = ParseOK !ParseState a
    | ParseFail !ParseError

data ParseError = ParseError {
        _parseErrorLocation :: Location,
        _parseErrorMessage  :: Doc ()
    }

{- Class instances: -}

instance Monad Parser where
    {-# INLINE return #-}
    return = returnParser

    {-# INLINE (>>=) #-}
    (>>=) = bindParser

    {-# INLINE (>>) #-}
    (>>) = thenParser

instance Fail.MonadFail Parser where
  fail = failParser . pretty

instance Functor Parser where
    {-# INLINE fmap #-}
    fmap = mapParser

instance Applicative Parser where
    {-# INLINE pure #-}
    pure = returnParser

    {-# INLINE (<*>) #-}
    (<*>) = appParser

instance MonadState ParseState Parser where
    {-# INLINE get #-}
    get = getParseState

    {-# INLINE put #-}
    put = putParseState

instance MonadError ParseError Parser where
    throwError = throwParser
    catchError = catchParser

prettyParseError :: ParseError -> Doc ()
prettyParseError err =
    pretty (_parseErrorLocation err) <> colon <+>
    _parseErrorMessage err

returnParser :: a -> Parser a
{-# INLINE returnParser #-}
returnParser x = Parser $ \s -> ParseOK s x

bindParser :: Parser a -> (a -> Parser b) -> Parser b
{-# INLINE bindParser #-}
bindParser (Parser m) f = Parser $ \s -> case m s of
    ParseFail e -> ParseFail e
    ParseOK s' x -> unParse (f x) s'

thenParser :: Parser a -> Parser b -> Parser b
{-# INLINE thenParser #-}
thenParser (Parser m) (Parser n) = Parser $ \s -> case m s of
    ParseFail e -> ParseFail e
    ParseOK s' _ -> n s'

mapParser :: (a -> b) -> Parser a -> Parser b
{-# INLINE mapParser #-}
mapParser f (Parser m) = Parser $ \s -> case m s of
    ParseFail e -> ParseFail e
    ParseOK s' x -> ParseOK s' (f x)

appParser :: Parser (a -> b) -> Parser a -> Parser b
{-# INLINE appParser #-}
appParser (Parser m) (Parser n) = Parser $ \s -> case m s of
    ParseFail e -> ParseFail e
    ParseOK s' f -> case n s' of
        ParseFail e' -> ParseFail e'
        ParseOK s'' x -> ParseOK s'' (f x)

failParser :: Doc () -> Parser a
failParser msg = Parser $ \s -> ParseFail ParseError {
        _parseErrorLocation = _parseLastLoc s,
        _parseErrorMessage = msg
    }

parseError :: Location -> Doc () -> Parser a
parseError loc msg = Parser $ \_ -> ParseFail ParseError {
        _parseErrorLocation = loc,
        _parseErrorMessage = msg
    }

getParseState :: Parser ParseState
{-# INLINE getParseState #-}
getParseState = Parser $ \s -> ParseOK s s

putParseState :: ParseState -> Parser ()
{-# INLINE putParseState #-}
putParseState s = Parser $ \_ -> ParseOK s ()

throwParser :: ParseError -> Parser a
throwParser err = Parser $ \_ -> ParseFail err

catchParser :: Parser a -> (ParseError -> Parser a) -> Parser a
catchParser (Parser m) handler = Parser $ \s -> case m s of
    ParseOK s' x -> ParseOK s' x
    ParseFail err -> unParse (handler err) s

returnEOF :: HasEOF a => Parser (Located a)
returnEOF = do
    pos <- getParsePosition
    let loc = mkLocation pos pos
    return $ Located loc mkEOF

{- Interface: -}

getParsePosition :: Parser Position
{-# INLINE getParsePosition #-}
getParsePosition = gets _parsePosition

getParseLocation :: Parser Location
{-# INLINE getParseLocation #-}
getParseLocation = gets _parseLastLoc

setParseLocation :: Location -> Parser ()
{-# INLINE setParseLocation #-}
setParseLocation loc = modify' $ \s -> s { _parseLastLoc = loc }

popParseAlexState :: Parser ()
popParseAlexState = modify' popAlexState
    where
        popAlexState s = s {
            _parseAlexState = tail $ _parseAlexState s
        }

topParseAlexState :: Parser AlexState
{-# INLINE topParseAlexState #-}
topParseAlexState = gets (head . _parseAlexState)

pushParseAlexState :: AlexState -> Parser ()
pushParseAlexState st = modify' pushAlexState
    where
        pushAlexState s = s {
            _parseAlexState = st : _parseAlexState s
        }

getLexInput :: Parser AlexInput
{-# INLINE getLexInput #-}
getLexInput = gets input
    where input s = AlexInput {
                _alexPos = _parsePosition s,
                _alexPrevChar = _parsePrevChar s,
                _alexInput = _parseInput s
            }

setLexInput :: AlexInput -> Parser ()
{-# INLINE setLexInput #-}
setLexInput (AlexInput pos c inp) =
    pos `seq` c `seq` inp `seq` modify' (\s -> s { _parsePosition = pos, _parsePrevChar = c, _parseInput = inp })
