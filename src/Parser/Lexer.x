{

{-# OPTIONS_GHC -w #-}

module Parser.Lexer (lexer, tokenEndPos) where

import Basic.Location
import Data.Char (chr)
import Parser.Alex
import Parser.LexAction
import Parser.Monad
import Parser.Tokens
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
$small              = [$ascsmall $unismall \_]

$bindigit           = 0-1
$octdigit           = 0-7
$decdigit           = 0-9
$hexdigit           = [$decdigit a-f A-F]

$unidigit           = \x3
$digit              = [$decdigit $unidigit]

$idfirst            = [$small $large]
$idtail             = [$idfirst $digit \']

$unisymbol          = \x04
$special            = [\(\)\,\;\[\]\`\{\}]
$ascsymbol          = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]
$symbol             = [$ascsymbol $unisymbol] # [$special \_\:\"\'\.]

@whitespace         = $whitechr+
@linecomment        = "//" $notnewline*
@varid              = $idfirst $idtail*
@varsym             = $symbol+
@binary             = $bindigit+
@octal              = $octdigit+
@decimal            = $decdigit+
@hexadecimal        = $hexdigit+
@backslash          = \\
@quote              = \" -- "

tokens :-
    <0> {
        @whitespace                 ;
        @linecomment                ;
        @quote                      { enterState' stringLiteral (tokSimple TokStartStringLiteral ) }
        "/*"[$symbol #\/]           { enterState comment lexToken }
        "/*"                        { enterState comment lexToken }
        "*/"                        { tokError "Closing comment without a corresponding opening comment." }
        "0b" @binary                { skip 2 (tokenInteger 2) }
        "0o" @octal                 { skip 2 (tokenInteger 8) }
        "0x" @hexadecimal           { skip 2 (tokenInteger 16) }
             @decimal               { tokenInteger 10 }

        -- Special:
        "->"                        { tokSimple TokArrow }
        "=>"                        { tokSimple TokDoubleArrow }
        "@"                         { tokSimple TokAt }
        "$"                         { tokSimple TokDollar }
        ";"                         { tokSimple TokSemiColon }
        "::"                        { tokSimple TokColonColon }
        ":"                         { tokSimple TokColon }
        ","                         { tokSimple TokComma }
        "."                         { tokSimple TokDot }
        ".."                        { tokSimple TokDotDot }
        "_"                         { tokSimple TokHole }

        -- Parenthesis:
        "("                         { tokSimple TokParenLeft }
        ")"                         { tokSimple TokParenRight }
        "["                         { tokSimple TokSquareLeft }
        "]"                         { tokSimple TokSquareRight }
        "{#"                        { tokSimple TokCurlyHashLeft }
        "{##"                       { tokSimple TokCurlyHashHashLeft }
        "{"                         { tokSimple TokCurlyLeft }
        "}"                         { tokSimple TokCurlyRight }
        ".("                        { tokSimple TokDotParen }

        -- Operators:
        "="                         { tokSimple TokAssign }
        "<="                        { tokSimple TokLte }
        "*"                         { tokSimple TokStar }
        "+"                         { tokSimple TokPlus }
        "!"                         { tokSimple TokExclam }

        -- Keywords:
        "arr"                       { tokSimple TokArr }
        "as"                        { tokSimple TokAs }
        "bool"                      { tokSimple TokBool }
        "break"                     { tokSimple TokBreak }
        "Challenge"                 { tokSimple TokChallenge }
        "continue"                  { tokSimple TokContinue }
        "Convertible"               { tokSimple TokConvertible }
        "dbg_assert_eq"             { tokSimple TokDbgAssertEq }
        "dbg_assert"                { tokSimple TokDbgAssert }
        "default"                   { tokSimple TokDefault }
        "Domain"                    { tokSimple TokDomain }
        "eff"                       { tokSimple TokEff }
        "else"                      { tokSimple TokElse }
        "ExtendedArithmetic"        { tokSimple TokExtendedArithmetic }
        "extern"                    { tokSimple TokExtern }
        "false"                     { tokSimple TokFalse }
        "Field"                     { tokSimple TokField }
        "fn"                        { tokSimple TokFn }
        "for"                       { tokSimple TokFor }
        "forall"                    { tokSimple TokForAll }
        "if"                        { tokSimple TokIf }
        "impl"                      { tokSimple TokImpl }
        "in"                        { tokSimple TokIn }
        "inf"                       { tokSimple TokInf }
        "infix"                     { tokSimple TokInfix }
        "infixl"                    { tokSimple TokInfixL }
        "infixr"                    { tokSimple TokInfixR }
        "let"                       { tokSimple TokLet }
        "list"                      { tokSimple TokList }
        "match"                     { tokSimple TokMatch }
        "mut"                       { tokSimple TokMut }
        "Nat"                       { tokSimple TokNat }
        "ObliviousChoice"           { tokSimple TokObliviousChoice }
        "PermutationCheck"          { tokSimple TokPermutationCheck }
        "post"                      { tokSimple TokPost }
        "pre"                       { tokSimple TokPre }
        "prover"                    { tokSimple TokProver }
        "pub"                       { tokSimple TokPub }
        "public"                    { tokSimple TokPublic }
        "Qualified"                 { tokSimple TokQualified }
        "rec"                       { tokSimple TokRec }
        "ref"                       { tokSimple TokRef }
        "return"                    { tokSimple TokReturn }
        "self"                      { tokSimple TokSelfId }
        "Self"                      { tokSimple TokSelfType }
        "sieve"                     { tokSimple TokSieve }
        "store"                     { tokSimple TokStore }
        "Stage"                     { tokSimple TokStage }
        "string"                    { tokSimple TokString }
        "struct"                    { tokSimple TokStruct }
        "trace"                     { tokSimple TokTrace }
        "true"                      { tokSimple TokTrue }
        "tuple"                     { tokSimple TokTuple }
        "type"                      { tokSimple TokType }
        "uint"                      { tokSimple TokUInt }
        "unchecked"                 { tokSimple TokUnchecked }
        "unit"                      { tokSimple TokUnit }
        "Unqualified"               { tokSimple TokUnqualified }
        "use"                       { tokSimple TokUse }
        "Vectors"                   { tokSimple TokVectors }
        "Vectorization"             { tokSimple TokVectorization }
        "verifier"                  { tokSimple TokVerifier }
        "where"                     { tokSimple TokWhere }
        "while"                     { tokSimple TokWhile }
        "wire"                      { tokSimple TokWire }
	"with"                      { tokSimple TokWith }
        "witness"                   { tokSimple TokWitness }
	"zip"                       { tokSimple TokZip }

        -- Identifiers:
        @varid                      { tokenIdentifier }

        -- Operators:
        @varsym                     { tokenSymbol }
    }

    <stringLiteral> {
        @quote                      { exitState' (tokSimple TokEndStringLiteral) }
        @backslash "n"              { tokSimple (TokChar '\n') }
        @backslash "t"              { tokSimple (TokChar '\t') }
        @backslash     @decimal     { skip 1 (tokenNumericChar 10) }
        @backslash "b" @binary      { skip 2 (tokenNumericChar 2) }
        @backslash "o" @octal       { skip 2 (tokenNumericChar 8) }
        @backslash "x" @hexadecimal { skip 2 (tokenNumericChar 16) }
        @backslash .                { skip 1 tokenChar }
        .                           { tokenChar }
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
tokenInteger base loc buf len = fmap TokInt <$> tokInteger base loc buf len

tokenChar :: Action LToken
tokenChar loc buf len = fmap TokChar <$> tokChar loc buf len

tokenNumericChar :: Integer -> Action LToken
tokenNumericChar base loc buf len = fmap (TokChar . chr . fromInteger) <$> tokInteger base loc buf len

tokenIdentifier :: Action LToken
tokenIdentifier loc buf len = fmap TokId <$> tokText loc buf len

tokenSymbol :: Action LToken
tokenSymbol loc buf len = fmap TokSymbol <$> tokText loc buf len

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
