{

{-# OPTIONS_GHC -w #-}

module CCC.Lexer (lexer, tokenEndPos) where

import Basic.Location
import CCC.Tokens
import Data.Char (chr)
import Parser.Alex
import Parser.LexAction
import Parser.Monad
import Support.Pretty

import Control.Applicative
import Data.Text (Text)

}

$unispace           = \x05
$whitechr           = [\ \n\r\t\f\v $unispace]
$newline            = [\n\r]
$notnewline         = ~ $newline

$unilarge           = \x01
$asclarge           = [A-Z]
$large              = [$asclarge $unilarge]

$unismall           = \x02
$ascsmall           = [a-z]
$small              = [$ascsmall $unismall \@\_]

$bindigit           = 0-1
$octdigit           = 0-7
$decdigit           = 0-9
$nzdecdigit         = 1-9
$hexdigit           = [$decdigit a-f A-F]

$unidigit           = \x3
$digit              = [$decdigit $unidigit]

$idfirst            = [$small $large]
$idtail             = [$idfirst $digit]

$unisymbol          = \x04
$special            = [\(\)\,\:\;]
$ascsymbol          = [\!\#\$\%\&\*\+\.\/\<\=\>\?\\\^\|\-\~]
$symbol             = [$ascsymbol $unisymbol] # [$special \_\"\'\.]

@whitespace         = $whitechr+
@linecomment        = "//" $notnewline*
@id                 = $idfirst $idtail*
@binary             = $bindigit+
@octal              = $octdigit+
@nzdecimal          = $nzdecdigit $decdigit*
@decimal            = "0" | @nzdecimal
@hexadecimal        = $hexdigit+

tokens :-
    <0> {
        @whitespace                 ;
        @linecomment                ;
        "/*"[$symbol #\/]           { enterState comment lexToken }
        "/*"                        { enterState comment lexToken }
        "*/"                        { tokError "Closing comment without a corresponding opening comment." }
        "0b" @binary                { skip 2 (tokenInteger 2) }
        "0o" @octal                 { skip 2 (tokenInteger 8) }
        "0x" @hexadecimal           { skip 2 (tokenInteger 16) }
             @decimal               { tokenInteger 10 }

        -- Special:
        ";"                         { tokSimple TokSemicolon }
        ":"                         { tokSimple TokColon }
        ","                         { tokSimple TokComma }
        "."                         { tokSimple TokDot } 

        -- Parenthesis:
        "("                         { tokSimple TokParenLeft }
        ")"                         { tokSimple TokParenRight }

        -- Keywords:
        "version"                   { tokSimple TokVersion }
        "configuration"             { tokSimple TokConfiguration }
        "@challenge"                { tokSimple TokChallenge }
        "@plugin_constraints"       { tokSimple TokConstraints }
        "@plugin"                   { tokSimple TokPlugin }
        "@type"                     { tokSimple TokType }
        "field"                     { tokSimple TokField }
        "ext_field"                 { tokSimple TokExtField }
        "ring"                      { tokSimple TokRing }
        "bitwise"                   { tokSimple TokBitwise }
        "less_than"                 { tokSimple TokLessThan }
        "greater_than"              { tokSimple TokGreaterThan }
        "equals"                    { tokSimple TokEquals }
        "is_mersenne"               { tokSimple TokMersenne }
        "is_proth"                  { tokSimple TokProth }
        "is_power_of_2"             { tokSimple TokPow2 }
        "@convert"                  { tokSimple TokConvert }
        "@out"                      { tokSimple TokOut }
        "@in"                       { tokSimple TokIn }
        "@begin"                    { tokSimple TokBegin }
        "@end"                      { tokSimple TokEnd }
        "@constraint"               { tokSimple TokConstraint }

        -- Identifiers:
        @id                         { tokenIdentifier }

    }

    <comment> {
        "/*"                        { enterState comment lexToken }
        "*/"                        { exitState lexToken }
        $newline                    ;
        .                           ;
    }

    .                               { tokError "Start of an unrecognized token" }

{

tokenInteger :: Integer -> Action LToken
tokenInteger base loc buf len = fmap TokInteger <$> tokInteger base loc buf len

tokenIdentifier :: Action LToken
tokenIdentifier loc buf len = fmap TokId <$> tokText loc buf len

lexToken :: Parser LToken
lexToken = do
    input <- getLexInput
    st <- topParseAlexState
    case alexScanUser () input st of
        AlexEOF -> returnEOF
        AlexError input' -> do
            let loc = mkLocation (_alexPos input) (_alexPos input')
            parseError loc $ pretty "Lexical error from Alex"
        AlexSkip input' len -> setLexInput (fixInput input input' len) >> lexToken
        AlexToken input' len action -> do
            let loc = mkLocation (_alexPos input) (_alexPos input')
            setLexInput (fixInput input input' len)
            setParseLocation loc
            action loc (_alexInput input) len

lexer :: (LToken -> Parser a) -> Parser a
lexer k = lexToken >>= k

tokenEndPos :: Int -> Int -> Text -> Maybe Position
tokenEndPos lineNo characterNo lineStr =
  case alexScanUser () input 0 of
    AlexToken input' _ _ -> Just $ _alexPos input'
    _ -> Nothing
  where
    input = AlexInput {
      _alexPos = Position {
          _posFilename = "",
          _posLine = lineNo,
          _posCol = characterNo
          }
      , _alexPrevChar = '\0'
      , _alexInput = lineStr
      }

}
