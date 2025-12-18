{

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module CCC.Parser (parse) where

import Basic.Location
import CCC.Lexer
import CCC.Syntax
import CCC.Tokens
import Parser.Monad
import Support.Pretty

import Data.Maybe (isJust, fromJust)
import Data.Text (Text)

}

%name parse CCC
%tokentype { LToken }
%monad { Parser }
%lexer { lexer } { Located _ TokEOF }

%token
    -- Special:
    ','                         { Located $$ TokComma }
    ':'                         { Located $$ TokColon }
    ';'                         { Located $$ TokSemicolon }
    '.'                         { Located $$ TokDot }

    -- Parenthesis:
    '('                         { Located $$ TokParenLeft }
    ')'                         { Located $$ TokParenRight }

    -- Keywords:
    'version'                   { Located $$ TokVersion }
    'configuration'             { Located $$ TokConfiguration }
    '@challenge'                { Located $$ TokChallenge }
    '@plugin'                   { Located $$ TokPlugin }
    '@type'                     { Located $$ TokType }
    'field'                     { Located $$ TokField }
    'ext_field'                 { Located $$ TokExtField }
    'ring'                      { Located $$ TokRing }
    'bitwise'                   { Located $$ TokBitwise }
    'less_than'                 { Located $$ TokLessThan }
    'greater_than'              { Located $$ TokGreaterThan }
    'equals'                    { Located $$ TokEquals }
    'is_mersenne'               { Located $$ TokMersenne }
    'is_proth'                  { Located $$ TokProth }
    'is_power_of_2'             { Located $$ TokPow2 }
    '@convert'                  { Located $$ TokConvert }
    '@out'                      { Located $$ TokOut }
    '@in'                       { Located $$ TokIn }
    '@begin'                    { Located $$ TokBegin }
    '@end'                      { Located $$ TokEnd }
    '@plugin_constraints'       { Located $$ TokConstraints }
    '@constraint'               { Located $$ TokConstraint }

    IDENT                       { Located _ (TokId _) }
    INT                         { Located _ (TokInteger _) }
    EOF                         { Located _ TokEOF }

%%

--
-- Useful utility rules:
--

Many1(prod)
    : prod             { [$1] }
    | Many1(prod) prod { $2 : $1 }

Many(prod)
    : {- nothing -}    { [] }
    | Many1(prod)      { $1 }

SepBy1(prod,sep)
    : prod                       { [$1] }
    | SepBy1(prod,sep) sep prod  { $3 : $1 }

SepBy(prod,sep)
    : {- nothing -}    { [] }
    | SepBy1(prod,sep) { $1 }

-- Allows trailing separator
SepByTrail(prod,sep)
    : {- nothing -}          { [] }
    | SepByTrail1(prod, sep) { $1 }

SepByTrail1(prod,sep)
    : SepBy1(prod, sep) Maybe(sep) { $1 }

Maybe(prod)
    : prod { Just $1 }
    | { Nothing }


--
-- Helpers
--

Int :: { Located Int }
  : INT { mkInt $1 }

Integer :: { Located Integer }
  : INT { mkInteger $1 }

Identifier :: { Located Text }
  : IDENT { mkIdentifier $1 }


-- 
-- CCC stuff
-- 

Plugin :: { Located (CCCPlugin Text) }
  : '@plugin' Identifier ';' { loc $1 $> (CCCPlugin (fmap extractVersion $2)) }

Predicate :: { Located CCCPred }
  : 'less_than' '(' Integer ')' { loc $1 $> (CCCLT $3) }
  | 'greater_than' '(' Integer ')' { loc $1 $> (CCCGT $3) }
  | 'equals' '(' Integer ')' { loc $1 $> (CCCEQ $3) }
  | 'is_mersenne' { loc $1 $> CCCMersenne }
  | 'is_proth' { loc $1 $> CCCProth }
  | 'is_power_of_2' { loc $1 $> CCCPow2 }

TypeVariant :: { CCCType Text }
  : 'field' '(' SepBy(Predicate,',') ')' { CCCField (reverse $3) }
  | 'ext_field' '(' SepBy1(Int,',') ')' '(' SepBy(Predicate,',') ')' '(' SepBy(Predicate,',') ')' 
    { CCCExtField (reverse $3) (reverse $6) (reverse $9) }
  | 'ring' '(' SepBy(Predicate,',') ')' { CCCRing (reverse $3) }
  | 'bitwise' '(' SepBy(Predicate,',') ')' { CCCBitwise (reverse $3) }
  | '@plugin' Identifier { CCCPluginType $2 }

Type :: { Located (CCCType Text) }
  : '@type' TypeVariant ';' { loc $1 $> $2 }

Challenge :: { Located CCCChallenge }
  : '@challenge' '(' Int ')' ';' { loc $1 $> (CCCChallenge $3) }

Conversion :: { Located CCCConversion }
  : '@convert' '(' '@out' ':' Int ',' '@in' ':' Int ')' ';' { loc $1 $> (CCCConversion $5 $9) }

ConstraintArg :: { Located (CCCConstraintArg Text) }
  : Identifier { loc $1 $> (CCCNameArg $1) }
  | Predicate { loc $1 $> (CCCPredArg $1) }
  | Integer { loc $1 $> (CCCNumArg $1) }

Constraint :: { Located (CCCConstraint Text) }
  : '@constraint' '(' SepBy(ConstraintArg,',') ')' ';' { loc $1 $> (CCCConstraint (reverse $3)) }

ConstraintBlock :: { Located (CCCConstraintBlock Text) }
  : '@plugin_constraints' '(' Identifier ')' Many(Constraint) '@end' { loc $1 $> (CCCConstraintBlock $3 (reverse $5)) }

Version :: { Located (Located Int , Located Int , Located Int) }
  : 'version' Int '.' Int '.' Int ';' { loc $1 $> ($2 , $4 , $6) }

CCC :: { CCC Text }
  : Version 
    'configuration' ';' 
    Many(Plugin)
    Many1(Type)
    Many(Challenge)
    Many(Conversion)
    Many(ConstraintBlock)
    { CCC $1 (reverse $4) (reverse $5) (reverse $6) (reverse $7) (reverse $8) }

{

joinLocs :: (HasLocation l, HasLocation r) => l -> r -> Location
joinLocs l r = joinLocations (location l) (location r)

loc :: (HasLocation l, HasLocation r, HasLocation a) => l -> r -> UnLocated a -> a
loc l r x = x `setLocation` joinLocs l r

nl :: Location
nl = NoLocation

--
-- Smart constructors for syntax tree:
-- (The constructors annotate the tree with correct locations)
--

mkInteger :: LToken -> Located Integer
mkInteger (Located l (TokInteger n)) = Located l n

mkInt :: LToken -> Located Int
mkInt (Located l (TokInteger n)) = Located l (fromInteger n)

mkIdentifier :: LToken -> Located Text
mkIdentifier (Located l (TokId x)) = Located l x

happyError :: Parser a
happyError = do
  loc <- getParseLocation
  parseError loc "Parse error."

}
