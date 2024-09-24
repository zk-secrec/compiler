{

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Parser.Parser (parse) where

import Basic.Location
import Basic.Name
import Basic.Fixity
import Parser.Effect
import Parser.Lexer
import Parser.Monad
import Parser.Syntax
import Parser.Tokens
import Support.Pretty

import Control.Lens (mapped, (&), (.~))
import Control.Monad (unless, forM_)
import Data.Maybe (maybe, fromMaybe, isJust)
import Data.Text (Text)
import Safe (lastDef)

}

%expect 12

%name parse Program
%tokentype { LToken }
%monad { Parser }
%lexer { lexer } { Located _ TokEOF }

%token
    '->'                 { Located $$ TokArrow }
    '=>'                 { Located $$ TokDoubleArrow }
    '@'                  { Located $$ TokAt }
    '$'                  { Located $$ TokDollar }
    ','                  { Located $$ TokComma }
    ':'                  { Located $$ TokColon }
    '::'                 { Located $$ TokColonColon }
    ';'                  { Located $$ TokSemiColon }
    '.'                  { Located $$ TokDot }
    '..'                 { Located $$ TokDotDot }
    '_'                  { Located $$ TokHole }

    -- Parenthesis:
    '('                  { Located $$ TokParenLeft }
    ')'                  { Located $$ TokParenRight }
    '['                  { Located $$ TokSquareLeft }
    ']'                  { Located $$ TokSquareRight }
    '{#'                 { Located $$ TokCurlyHashLeft }
    '{##'                { Located $$ TokCurlyHashHashLeft }
    '{'                  { Located $$ TokCurlyLeft }
    '}'                  { Located $$ TokCurlyRight }
    '.('                 { Located $$ TokDotParen }

    -- Operators:
    '='                  { Located $$ TokAssign }
    '<='                 { Located $$ TokLte }
    '*'                  { Located $$ TokStar }
    '+'                  { Located $$ TokPlus }
    '!'                  { Located $$ TokExclam }

    -- Keywords:
    'arr'                { Located $$ TokArr }
    'as'                 { Located $$ TokAs }
    'bool'               { Located $$ TokBool }
    'break'              { Located $$ TokBreak }
    'Challenge'          { Located $$ TokChallenge }
    'continue'           { Located $$ TokContinue }
    'Convertible'        { Located $$ TokConvertible }
    'dbg_assert_eq'      { Located $$ TokDbgAssertEq }
    'dbg_assert'         { Located $$ TokDbgAssert }
    'default'            { Located $$ TokDefault }
    'Domain'             { Located $$ TokDomain }
    'eff'                { Located $$ TokEff }
    'else'               { Located $$ TokElse }
    'ExtendedArithmetic' { Located $$ TokExtendedArithmetic }
    'extern'             { Located $$ TokExtern }
    'false'              { Located $$ TokFalse }
    'Field'              { Located $$ TokField }
    'fn'                 { Located $$ TokFn }
    'for'                { Located $$ TokFor }
    'forall'             { Located $$ TokForAll }
    'if'                 { Located $$ TokIf }
    'impl'               { Located $$ TokImpl }
    'in'                 { Located $$ TokIn }
    'inf'                { Located $$ TokInf }
    'infix'              { Located $$ TokInfix }
    'infixl'             { Located $$ TokInfixL }
    'infixr'             { Located $$ TokInfixR }
    'let'                { Located $$ TokLet }
    'list'               { Located $$ TokList }
    'match'              { Located $$ TokMatch }
    'mut'                { Located $$ TokMut }
    'Nat'                { Located $$ TokNat }
    'ObliviousChoice'    { Located $$ TokObliviousChoice }
    'PermutationCheck'   { Located $$ TokPermutationCheck }
    'post'               { Located $$ TokPost }
    'pre'                { Located $$ TokPre }
    'prover'             { Located $$ TokProver }
    'pub'                { Located $$ TokPub }
    'public'             { Located $$ TokPublic }
    'Qualified'          { Located $$ TokQualified }
    'rec'                { Located $$ TokRec }
    'ref'                { Located $$ TokRef }
    'return'             { Located $$ TokReturn }
    'Self'               { Located $$ TokSelfType }
    'self'               { Located $$ TokSelfId }
    'sieve'              { Located $$ TokSieve }
    'Stage'              { Located $$ TokStage }
    'store'              { Located $$ TokStore }
    'string'             { Located $$ TokString }
    'struct'             { Located $$ TokStruct }
    'trace'              { Located $$ TokTrace }
    'true'               { Located $$ TokTrue }
    'tuple'              { Located $$ TokTuple }
    'type'               { Located $$ TokType }
    'uint'               { Located $$ TokUInt }
    'unchecked'          { Located $$ TokUnchecked }
    'Unqualified'        { Located $$ TokUnqualified }
    'use'                { Located $$ TokUse }
    'Vectors'            { Located $$ TokVectors }
    'Vectorization'      { Located $$ TokVectorization }
    'verifier'           { Located $$ TokVerifier }
    'where'              { Located $$ TokWhere }
    'while'              { Located $$ TokWhile }
    'wire'               { Located $$ TokWire }
    'with'               { Located $$ TokWith }
    'witness'            { Located $$ TokWitness }
    'zip'                { Located $$ TokZip }

    STRSTART             { Located $$ TokStartStringLiteral }
    STREND               { Located $$ TokEndStringLiteral }

    OPER                 { Located _ (TokSymbol _) }

    IDENT                { Located _ (TokId _) }
    INT                  { Located _ (TokInt _) }
    CHAR                 { Located _ (TokChar _) }

%right '='
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
-- Expressions:
--

ExprWithoutBlock :: { Expr Text }
    : AssignExpr { $1 }

AssignExpr :: { Expr Text }
    : LoadExpr0 '=' Maybe('.') Expr { Assign (mkIsVectorized $3) $1 $4 }
    | LoadExpr0 '{#' Expr '}' '=' Expr { 
        mkCallExpr NotVectorized (Func (Located (location $1) "store_write")) [] [RefArg $1, $3, $6] (location $6) 
    }
    | LamExpr { $1 }

LamExpr :: { Expr Text }
    : FuncStart '(' SepByTrail(LamParam, Comma) ')' LamReturnType Expr { Lam (unLocated $1) (reverse $3) $5 $6 }
    | BinExpr { $1 }

LamParam :: { LamParam Text }
    : Identifier ':' Type { LamParam $1 (Just $3) }
    | Identifier { LamParam $1 Nothing }

LamReturnType :: { Maybe (Type Text) }
    : '->' Type { Just $2 }
    | {- empty -} { Nothing }

BinExpr :: { Expr Text }
    : CastOrAscriptionExpr Oper Maybe('.') ExprWithoutStruct { mkCallOper (mkIsVectorized $3) $2 [$1, $4] }
    | CastOrAscriptionExpr { $1 }

CastOrAscriptionExpr :: { Expr Text }
    : BinExpr 'as' Type { loc $1 $3 (Cast $1 $3)  }
    | BinExpr ':' Type { Ascription $1 $3 }
    | UnaryExpr { $1 }

UnaryExpr :: { Expr Text }
    : Oper Maybe('.') UnaryExpr { mkCallOper (mkIsVectorized $2) $1 [$3] }
    | TypePredExpr { $1 }
    | DbgAssertExpr { $1 }

DbgAssertExpr :: { Expr Text }
    : 'dbg_assert' '(' Expr ')' { loc $1 $> (DbgAssert $3 Nothing) }
    | 'dbg_assert' '(' Expr ',' Expr ')' { loc $1 $> (DbgAssert $3 (Just $5)) }
    | 'dbg_assert_eq' '(' Expr ',' Expr ')' { loc $1 $> (DbgAssertEq $3 $5 Nothing) }
    | 'dbg_assert_eq' '(' Expr ',' Expr  ',' Expr ')' { loc $1 $> (DbgAssertEq $3 $5 (Just $7)) }
    | LoadExpr { $1 }

LoadExpr0 :: { Expr Text }
    : LoadExpr0 '[' Slice ']' { loc $1 $> (Index $1 $3) }
    | LoadExpr0 '{##' Expr '}' { loc $1 $> (IndexStore $1 $3) }
    | LoadExpr0 '.' Selector { loc $1 $> (Select $1 (unLocated $3)) }
    | AppExpr { $1 }

LoadExpr :: { Expr Text }
    : LoadExpr0 { $1 }
    | LoadExpr0 '{#' Expr '}' { mkCallExpr NotVectorized (Func (Located (location $1) "store_read")) [] [RefArg $1, $3] $4 }

AppExpr :: { Expr Text }
    : CallExpr { $1 }
    | PrimaryExpr { $1 }

Selector :: { Located Selector }
    : Identifier { Located (location $1) (SelectField (unLocated $1)) }
    | Integer { Located (location $1) (SelectIndex (fromInteger (unLocated $1))) }

PrimaryExpr :: { Expr Text }
    : Variable { $1 }
    | Bit { $1 }
    | Integer { loc $1 $1 (Lit (ConstInt (unLocated $1))) }
    | StringLiteralExpr { $1 }
    | MakeList { $1 }
    | MakeStore { $1 }
    | MakeTuple { $1 }
    | '(' Expr ')' {
        -- Note: Doubled location annotation is necessary!
        -- We use this to detect where actual parethesis are placed.
        -- This is used by shunting-yard.
        ExprLoc (joinLocations $1 $3) (loc $1 $3 $2)
    }
    | 'self' { ExprLoc $1 Self }
    | '_' { Hole }

Bit :: { Expr Text }
    : 'true' { loc $1 $1 (Lit (ConstBool True)) }
    | 'false' { loc $1 $1 (Lit (ConstBool False)) }

StringLiteralExpr :: { Expr Text }
    : Many1(SingleStringLiteral) { mkCompoundStringLiteralExpr (reverse $1) }

StringLiteral :: { Located String }
    : Many1(SingleStringLiteral) { mkCompoundStringLiteral (reverse $1) }

SingleStringLiteral :: { Located String }
    : StrStart Many(Char) StrEnd { loc $1 $3 (reverse $2) }

Variable :: { Expr Text }
    : Identifier { ExprLoc (location $1) (Var $1) }

TypeArguments :: { [TypeArgument Text] }
    : SepByTrail(TypeArgument, Comma) {
        reverse $1
    }

CallExpr :: { Expr Text }
    : Identifier ArgsBegin SepByTrail(RefArg, Comma) ')' { 
        mkCallExpr (mkIsVectorized $2) (Func $1) [] (reverse $3) $> 
    } 
    | Identifier '::' '[' TypeArguments ']' ArgsBegin SepByTrail(RefArg, Comma) ')' {
        mkCallExpr (mkIsVectorized $6) (Func $1) $4 (reverse $7) $>
    }

ArgsBegin :: { Maybe () }
    : '('  { Nothing }
    | '.(' { Just () }
{-
FuncOrMethod :: { FuncOrMethod Text }
    : Identifier { Func $1 }
    | LoadExpr '.' Identifier { Method $1 $3 }
-}
RefArg :: { Expr Text }
    : 'ref' Expr { loc $1 $> (RefArg $2) }
    | Expr { $1 }

StructFieldCtor :: { StructFieldCtor Text }
    : Identifier ':' Expr { StructFieldCtor $1 $3 }

StructCtor :: { Expr Text }
    : Identifier '{' SepByTrail(StructFieldCtor, Comma) '}' {
        loc $1 $> (StructCtor $1 [] (reverse $3))
    }
    | Identifier '::' '[' TypeArguments ']' '{' SepByTrail(StructFieldCtor, Comma) '}' {
        loc $1 $> (StructCtor $1 $4 (reverse $7))
    }

TypeArgument :: { TypeArgument Text }
    : Type { TypeArg $1 }
    | Identifier '=' Type { TypeArgNamedType $1 $3 }
    | '@' Identifier '=' DomainType { TypeArgNamedType $2 $4 }
    | Identifier '@' Identifier '=' Type { TypeArgQualifiedNamedType $1 $3 $5 }

Slice :: { LArraySlice (Expr Text) }
    : Expr { Located (location $1) (ArrayIndex $1) }
    | Expr '..' Expr { loc $1 $3 (ArrayFromTo $1 $3) }
    | Expr '..' { loc $1 $2 (ArrayFrom $1) }
    | '..' Expr { loc $1 $2 (ArrayTo $2) }
    | '..' { Located $1 ArrayAll }

MakeList :: { Expr Text }
    : '[' Expr ';' Expr ']' { loc $1 $> (List (ListReplicate $2 $4)) }
    | '[' Expr '..' Expr ']' { loc $1 $> (List (ListRange $2 $4)) }
    | '[' SepByTrail(Expr, Comma) ']' { loc $1 $> (List (ListElems (reverse $2))) }

KeyValuePair :: { (Expr Text, Expr Text) }
    : Expr '=>' Expr { ($1, $3) }

MakeStore :: { Expr Text }
    : '{##' SepByTrail(KeyValuePair, Comma) '}' {
        loc $1 $> (StoreCtor (reverse $2))
    }
    | '{#' '}' {
        mkCallExpr NotVectorized (Func (Located $1 "store_new_def")) [] [] $2
    }

MakeTuple :: { Expr Text }
    : '(' SepByTrail1(Expr, Comma) ')' { loc $1 $> (Tuple (reverse $2)) }

-- Limited form of predicates that can occur in expressions.
TypePredExpr :: { Expr Text }
    : SpecialTypePred { TypePredExpr $1 `setLocation` location $1 }
    | CCCTypePred { TypePredExpr $1 `setLocation` location $1 }
    
BlockExpr :: { Expr Text }
    : '{' BlockStatements '}' { loc $1 $> (mkBlock $2) }
    | '{' BlockStatements ExprWithoutBlock '}' { loc $1 $> (mkBlock (Left $3 : $2)) }
    | '{' BlockStatements StructCtor '}' { loc $1 $> (mkBlock (Left $3 : $2)) }

BlockStatements :: { [Either (Expr Text) (Stmt Text)] }
    : {- nothing -} { [] }
    | BlockStatements Statement { $2 : $1 }

IfThenElseExpr :: { Expr Text }
    : 'if' Expr BlockExpr { loc $1 $> (IfThenElse $2 $3 Nothing) }
    | 'if' Expr BlockExpr 'else' BlockExpr { loc $1 $> (IfThenElse $2 $3 (Just $5)) }
    | 'if' Expr BlockExpr 'else' IfThenElseExpr {
        loc $1 $> (IfThenElse $2 $3 (Just $5))
    }

MatchExpr :: { Expr Text }
    : 'match' Expr '{' SepBy1(Case, Comma) '}' { 
        let (litcases , defcases) = span (isLitPat . unLocated . fst) (reverse $4) in
        loc $1 $> (Match $2 (litcases ++ (if null defcases then [(noLoc WildCard, mkAssertFalse)] else defcases)))
      }

Case :: { (Located (Pat Text), Expr Text) }
    : Pat '=>' BlockExpr { ($1, $3) }

Pat :: { Located (Pat Text) }
    : Integer    { fmap LitPat $1 }
    | Identifier { fmap VarPat $1 }
    | '_'        { Located $1 WildCard }

ForExpr :: { Expr Text }
    : 'for' Identifier 'in' Expr '..' ExprWithoutStruct BlockExpr { loc $1 $> (For $2 $4 $6 $7) }

ZipExprIter :: { (Located Text, Expr Text) }
    : Identifier 'in' Expr { ($1, $3) }

ZipExpr :: { Expr Text }
    : 'zip' SepBy1(ZipExprIter, Comma) 'with' BlockExpr { Zip (reverse $2) $4 }

WhileExpr :: { Expr Text }
    : 'while' ExprWithoutStruct BlockExpr { loc $1 $> (While $2 $3) }

TraceExpr :: { Expr Text }
    : 'trace' StringLiteral BlockExpr { loc $1 $> (Trace $2 $3) }

-- Check for legacy 'witness' keyword.
WitnessOrWire :: { Location }
    : 'witness' {% parseError $1 "Keyword 'witness' no longer supported. Use 'wire' instead." }
    | 'wire' { $1 }

WireExpr :: { Expr Text }
    : WitnessOrWire BlockExpr {
        let unitExpr = Ascription (Lit ConstUnit) mkTypeUnit in
        loc $1 $> (WireExpr unitExpr $2)
    }
    | WitnessOrWire '(' Expr ')' BlockExpr {% parseError (joinLocs $2 $4) "Shape argument no longer supported in wire expressions" }
{-         return (loc $1 $> (WireExpr $3 $5) ) -}
    | WitnessOrWire MakeList BlockExpr {% parseError (location $2) "Shape argument no longer supported in wire expressions" }
{-         return (loc $1 $> (WireExpr $2 $3)) -}

ExprWithBlock :: { Expr Text }
    : BlockExpr { $1 }
    | IfThenElseExpr { $1 }
    | MatchExpr { $1 }
    | ForExpr { $1 }
    | ZipExpr { $1 }
    | WhileExpr { $1 }
    | TraceExpr { $1 }
    | WireExpr { $1 }

ExprWithoutStruct :: { Expr Text }
    : ExprWithBlock { $1 }
    | ExprWithoutBlock { $1 }

Expr :: { Expr Text }
    : ExprWithoutStruct { $1 }
    | StructCtor { $1 }

--
-- Types:
--

PrimType :: { Type Text }
    : StageType { $1 }
    | DomainType { $1 }
    | NaturalType { $1 }
    | BoolType { $1 }
    | 'string' { TCon ConString $1 }
    | '(' ')' { TCon ConUnit (joinLocations $1 $2) }
    | UIntType { $1 }
    | ArrType { $1 }
    | ListType { $1 }
    | TupleType { $1 }
    | StoreType { $1 }
    | TypeVariable { $1 }
    | '(' Type ')' { loc $1 $> $2 }
    | 'Self' { TSelf (location $1) }
    | '_' { TCon ConHole $1 }

Type :: { Type Text }
    : FunType { $1 }

FunType :: { Type Text }
    : QualifiedType '->' FunType { loc $1 $> (mkFunArgs [$1] $3) }
    | QualifiedType { $1 }

QualifiedType :: { Type Text }
    : PrimType StageType    DomainType   { mkQualifiedType $1 $2 $3 }
    | PrimType StageType    TypeVariable { mkQualifiedType $1 $2 $3 }
    | PrimType TypeVariable DomainType   { mkQualifiedType $1 $2 $3 }
    | PrimType TypeVariable TypeVariable { mkQualifiedType $1 $2 $3 }
    | PrimType StageType                 { mkQualifiedType $1 $2 mkNoDomain }
    | PrimType              DomainType   { mkQualifiedType $1 mkNoStage $2 }
    | PrimType                           { $1 }

TypeVariable :: { Type Text }
    : Identifier { TVar (unLocated $1) KindUnknown (location $1) }
    | Identifier '[' SepByTrail1(Type, Comma) ']' {
        let varLoc = joinLocations (location $1) $2 in
        let argsLoc = joinLocations $2 $> in
        TApp (TVar (unLocated $1) KindUnknown varLoc) (reverse $3) argsLoc
    }

DomainType :: { Type Text }
    : '@' 'prover' { mkDomain ConProver $1 $2 }
    | '@' 'public' { mkDomain ConPublic $1 $2 }
    | '@' 'verifier' { mkDomain ConVerifier $1 $2 }
    | '@' '_' {mkDomain ConHole $1 $2}
    | '@' Identifier {
        TVar (unLocated $2) KindDomain (joinLocations $1 (location $2))
    }

StageType :: { Type Text }
    : '$' 'pre' { mkStage ConPre $1 $2 }
    | '$' 'post' { mkStage ConPost $1 $2 }
    | '$' '_' {mkStage ConHole $1 $2}
    | '$' Identifier {
        TVar (unLocated $2) KindStage (joinLocations $1 (location $2))
    }

ArrType :: { Type Text }
    : 'arr' '[' Type Maybe(Comma) ']' {
        mkArrType $3 $1 $>
    }

ListType :: { Type Text }
    : 'list' '[' Type Maybe(Comma) ']' {
        mkListType $3 $1 $>
    }

StoreType :: { Type Text }
    : 'store' '[' Type ',' Type ']' {
        TApp (TCon ConStore $1) [$3, $5] (joinLocations $1 $>)
    }

TupleType :: { Type Text }
    : 'tuple' '[' SepByTrail1(Type, Comma) ']' {
        TApp (TCon (ConTuple (length $3)) $1) (reverse $3) (joinLocations $1 $>)
    }

-- Shift/reduce conflict is OK because of longest parse rule.
BoolType :: { UnqualifiedType Text }
    : 'bool' {
        TApp (TCon ConBool $1) [TCon (ConNat Infinite) $1] $1
    }
    | 'bool' '[' ModulusType ']' {
        TApp (TCon ConBool $1) [$3] (joinLocations $1 $>)
    }

-- Shift/reduce conflict is OK because of longest parse rule.
UIntType :: { UnqualifiedType Text }
    : 'uint' {
        TApp (TCon ConUInt $1) [TCon (ConNat Infinite) $1] $1
    }
    | 'uint' '[' ModulusType ']' {
        TApp (TCon ConUInt $1) [$3] (joinLocations $1 $>)
    }

ModulusType :: { NatType Text }
    : NaturalType { $1 }
    | Identifier { TVar (unLocated $1) KindNat (location $1) }

NaturalType :: { NatType Text }
    : Integer {
        let n = fromInteger (unLocated $1) in
        TCon (ConNat (Finite n)) (location $1)
    }
    | 'inf' {
        TCon (ConNat Infinite) $1
    }

--
-- Statements:
--

Statement :: { Either (Expr Text) (Stmt Text) }
    : 'break' ';' { Right (Break $1) }
    | 'continue' ';' { Right (Continue $1) }
    | 'return' Expr ';' { Right (Return $2) }
    | Let ';' { Right $1 }
    | ExprWithoutBlock ';' { Right (Expr $1) }
    | ExprWithBlock ';' { Right (Expr $1) }
    | ExprWithBlock { Left $1 }

Let :: { Stmt Text }
    : 'let' RecursionAttribute Binding BindingValue { Let $2 $3 $4 }

Binding :: { Binding Text}
    :  Mutability Identifier Maybe(BindingType) { Binding $1 $2 $3 }

RecursionAttribute :: { Bool }
    : {- nothing -} { False }
    | 'rec' { True }

Mutability :: { Mutability }
    : {- nothing -} { Immutable }
    | 'mut' { Mutable }

BindingType :: { Type Text }
    : ':' Type { $2 }

BindingValue :: { Expr Text }
    : '=' Expr { $2 }

--
-- Top-level:
--

Program :: { LProgram Text }
    : Many(TopLevel) {% mkProgram $1 }

TopLevel :: { TopLevel Text }
    : FunctionOrExtern { $1 }
    | EffectDecl FunctionOrExtern { $2 & traverseEffInTopLevel .~ Just $1 }
    | TypeDef { $1 }
    | Import { $1 }
    | StructDecl { $1 }
    | StructImpl { $1 }
    | Default { $1 }
{- -- old clauses
FunctionOrExtern :: { TopLevel Text }
    : EffectDecl Export(ExtStart) Signature ';' { 
        TopExtern (mkExtern (unLocated $2) (location $2) (Located (location $3) ((unLocated $3) {_sigEffect = Just $1})))
    }
    | EffectDecl Export(FuncStart) Signature BlockExpr {
        TopFunction (mkFunction (unLocated $2) (location $2) (Located (location $3) ((unLocated $3) {_sigEffect = Just $1})) $4)
    }
-}
FunctionOrExtern :: { TopLevel Text }
    : Function { $1 }
    | Extern { $1 }

Function :: { TopLevel Text }
    : Export(FuncStart) Signature BlockExpr {
        TopFunction (mkFunction (unLocated $1) (location $1) $2 $3)
    }

Extern :: { TopLevel Text }
    : Export(ExtStart) Signature ';' {
        TopExtern (mkExtern (snd (unLocated $1)) (location $1) $2)
    }

EffectDecl :: { Located (PolymorphicTypeWithEffect Text) }
    : 'unchecked' 'eff' 'forall' Many(Identifier) '.' TypeWithEffect { loc $1 $2 (PolyTwe (reverse (map unLocated $4)) $6) }
    | 'unchecked' 'eff' TypeWithEffect { loc $1 $2 (PolyTwe [] $3) }

PrimTypeWithEffect :: { TypeWithEffect' Text Text }
    : '*' { TweAny }
    | '[' SepBy(TypeWithEffect, Comma) ']' { TweTuple (reverse $2) }
    | '(' TypeWithEffect ')' { $2 }

TypeWithEffect :: { TypeWithEffect' Text Text }
    : PrimTypeWithEffect { $1 }
    | PrimTypeWithEffect '->' TypeWithEffect { TweFun $1 $3 mkEffectEmpty [] }
    | PrimTypeWithEffect '->' PrimTypeWithEffect '!' SepBy1(Type, Plus) {% do
        let ts = reverse $5
        forM_ ts $ \ case
          TDomain _  -> return ()
          TStage _   -> return ()
          TKBool _   -> return ()
          TVar _ k _
            | k `elem` [KindDomain, KindStage, KindBool]
                     -> return ()
          t          -> parseError (location t) "Types other than domains, stages and type level booleans not allowed as effects"
        return $ TweFun $1 $3 (mconcat (map mkEffect ts)) [] 
      }

FuncStart :: { Located IsSieveFn }
    : 'fn' { Located $1 NotSieveFn }
    | 'sieve' 'fn' { Located $1 IsSieveFn }

ExtStart :: { Location }
    : 'extern' 'fn' { joinLocations $1 $2 }

Signature :: { LSignature Text }
    : FuncIdentifier TypeParams FuncParams ReturnType Maybe(Fixity) Constraints { mkSignature $1 $2 $3 $4 $5 $6 }

FuncIdentifier :: { Located (FuncIdentifier Text) }
    : Identifier  { fmap FunctionId $1 }
    | Oper        { fmap OperatorId $1 }

ReturnType :: { Type Text }
    : '->' Type { $2 }
    | {- empty -} { mkTypeUnit }

FuncParams :: { Located [FuncParam Text] }
    : '(' SepByTrail(FuncParam, Comma) ')' { loc $1 $> (reverse $2) }

TypeParams :: { Located [TypeParam Text] }
    : '[' SepByTrail(TypeParam, Comma) ']' { loc $1 $> (reverse $2) }
    | {- empty -} { loc NoLocation NoLocation [] }

TypeParam :: { TypeParam Text }
    :  Identifier ':' Kind { TypeParam $1 (unLocated $3) }
    | '$' Identifier { TypeParam $2 KindStage }
    | '@' Identifier { TypeParam $2 KindDomain }
    | Identifier '@' Identifier { TypeParamQualify $1 Nothing $3 }
    | Identifier '$' Identifier '@' Identifier { TypeParamQualify $1 (Just $3) $5 }

FuncParam :: { FuncParam Text }
    : 'ref' Identifier ':' Type { FuncParam PassByRef $2 $4 }
    |       Identifier ':' Type { FuncParam PassByValue $1 $3 }
    | 'ref' 'self' { SelfParam PassByRef $2 }
    |       'self' { SelfParam PassByValue $1 }

TypeDef :: { TopLevel Text }
    : Export('type') Identifier TypeParams ':' Kind '=' Type Constraints ';' {
        TopTypeDef (mkTypeDef (location $1) $> $2 (snd $ unLocated $1) $3 $5 $8 $7)
    }

StructFieldDecl :: { StructFieldDecl Text }
    : Identifier ':' Type { StructFieldDecl $1 $3 }

StructDecl :: { TopLevel Text }
    : Export('struct') Identifier TypeParams '{' SepByTrail(StructFieldDecl, Comma) '}' {
        let decl = StructDecl $2 (snd $ unLocated $1) (unLocated $3) (reverse $5) in
        TopStructDecl (loc $1 $> decl)
    }

StructImpl :: { TopLevel Text }
    : 'impl' TypeParams Type '{' Many(Function) '}' {
        let topLevelToLFunction (TopFunction f) = f in
        let impl = StructImpl $2 $3 (map topLevelToLFunction $ reverse $5) in
        TopStructImpl (loc $1 $> impl)
    }

Kind :: { Located Kind }
    : AtomicKind   { $1 }
    | CompoundKind { $1 }

AtomicKind :: { Located Kind }
    : 'Qualified'    { Located $1 KindStar }
    | 'Unqualified'  { Located $1 KindUnqualified }
    | 'Domain'       { Located $1 KindDomain }
    | 'Stage'        { Located $1 KindStage }
    | 'Nat'          { Located $1 KindNat }
    | '(' Kind ')'   { Located (joinLocs $1 $>) (unLocated $2) }

CompoundKind :: { Located Kind }
    : AtomicKind '->' Kind { Located (joinLocs $1 $>) (unLocated $1 `KindFun` unLocated $3) }

Constraints :: { Located [TypePred Text] }
    : 'where' SepByTrail(TypePredicate, Comma) {
        let endLoc = lastDef NoLocation (map location $2) in
        loc $1 endLoc (reverse $2)
    }
    | {- empty -} { noLoc [] }

TypePredicate :: { TypePred Text }
    : 'default' Identifier '=' Type { mkPredDef $1 (location $>) $2 KindUnqualified $4 }
    | 'default' '@' Identifier '=' DomainType { mkPredDef $1 (location $>) $3 KindDomain $5 }
    | SpecialTypePred { $1 }
    | CCCTypePred { $1 }
    | 'Vectorization' { TypePred PConVectorization [] (location $1) }
    | Identifier '[' SepByTrail1(Type, Comma) ']' {% do
        -- TODO: Extend this to accept TypeArgument?
        let loc = joinLocs $1 $>
        let ident = unLocated $1
        let tys = reverse $3
        case ident of
          "Field"       -> return $ TypePred PConField tys loc
          "Convertible" -> return $ TypePred PConConvertible tys loc
          "SizedType"   -> return $ TypePred PConSized tys loc
          "Array"       -> return $ TypePred PConArray tys loc
          "Challenge"   -> return $ TypePred PConChallenge tys loc
          _             -> parseError (location $1) "Invalid type predicate."
     }
   | Identifier {% do
       let loc = location $1
       let ident = unLocated $1
       case ident of
         "Vectorization"      -> return $ TypePred PConVectorization [] loc
         "ObliviousChoice"    -> return $ TypePred PConObliviousChoice [] loc
         "ExtendedArithmetic" -> return $ TypePred PConExtendedArithmetic [] loc
         "PermutationCheck"   -> return $ TypePred PConPermutationCheck [] loc
         "Vectors"            -> return $ TypePred PConVectors [] loc
         _                    -> parseError (location $1) "Invalid type predicate."
     }

SpecialTypePred :: { TypePred Text }
    : 'pre' StageType { TypePred PConPre [$2] (joinLocs $1 $>) }
    | 'post' StageType { TypePred PConPost [$2] (joinLocs $1 $>) }
    | DomainType '<=' DomainType { TypePred PConSub [$1, $3] (joinLocs $1 $>) }

CCCTypePred :: { TypePred Text }
    : 'Field' '[' ModulusType ']' { TypePred PConField [$3] (joinLocs $1 $>) }
    | 'Challenge' '[' ModulusType ']' { TypePred PConChallenge [$3] (joinLocs $1 $>) }
    | 'Convertible' '[' ModulusType ',' ModulusType ']' { TypePred PConConvertible [$3, $5] (joinLocs $1 $>) }
    | 'ExtendedArithmetic' { TypePred PConExtendedArithmetic [] (location $1) }
    | 'PermutationCheck' { TypePred PConPermutationCheck [] (location $1) }
    | 'Vectors' { TypePred PConVectors [] (location $1) }
    | 'ObliviousChoice' { TypePred PConObliviousChoice [] (location $1) }

Fixity :: { Located Fixity }
    : 'infixl' Integer { Located $1 (Fixity LeftAssoc (unLocated $2)) }
    | 'infixr' Integer { Located $1 (Fixity RightAssoc (unLocated $2)) }
    | 'infix' Integer  { Located $1 (Fixity NonAssoc (unLocated $2)) }

Import :: { TopLevel Text }
    : 'use' Identifier '::' '*' ';' {% do
        return $ TopImport $ loc $1 $> (Import $ unLocated $2)
    }

Export(Item)
    : 'pub' Item { Located (joinLocs $1 $2) ($2 , True) }
    | Item { Located (location $1) ($1 , False) }

Default :: { TopLevel Text }
    : 'default' '(' SepByTrail(Type, ',') ')' ';' { TopDefault $ loc $1 $> $ Default $ reverse $3 }

--
-- Helpers for few terminals:
--

Char :: { Char }
    : CHAR { mkChar $1 }

Integer :: { Located Integer }
    : INT { mkInteger $1 }

Identifier :: { Located Text }
    : IDENT { mkIdentifier $1 }

Oper :: { Located Text }
    : OPER { mkOper $1 }
    | '<=' { Located $1 "<=" }
    | '*' { Located $1 "*" }
    | '+' { Located $1 "+" }
    | '!' { Located $1 "!" }

StrStart :: { Location }
    : STRSTART { $1 }

StrEnd :: { Location }
    : STREND { $1 }

Comma :: { Location }
    : ',' { $1 }

Plus :: { Location }
    : '+' { $1 }

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
mkInteger (Located l (TokInt n)) = Located l n

toStmt :: Either (Expr a) (Stmt a) -> Stmt a
toStmt (Left e) = Expr e
toStmt (Right stmt) = stmt

mkBlock :: [Either (Expr a) (Stmt a)] -> Expr a
mkBlock (Left e : stmts) = Block (reverse (map toStmt stmts)) (Just e)
mkBlock stmts = Block (reverse (map toStmt stmts)) Nothing

mkCompoundStringLiteralExpr :: [Located String] -> Expr Text
mkCompoundStringLiteralExpr strs = ExprLoc l (Lit (ConstString str))
  where Located l str = mkCompoundStringLiteral strs

mkCompoundStringLiteral :: [Located String] -> Located String
mkCompoundStringLiteral strs = loc firstLoc lastLoc (concatMap unLocated strs)
  where
    firstLoc = location (head strs)
    lastLoc = location (last strs)

mkIdentifier :: LToken -> Located Text
mkIdentifier (Located l (TokId x)) = Located l x

mkChar :: LToken -> Char
mkChar (Located _ (TokChar c)) = c

mkExportFlag :: Maybe a -> Bool
mkExportFlag = maybe False (\ _ -> True)

mkIsVectorized :: Maybe a -> IsVectorized
mkIsVectorized = maybe NotVectorized (\ _ -> IsVectorized)

mkOper :: LToken -> Located Text
mkOper (Located l (TokSymbol op)) = Located l op

mkCallOper :: IsVectorized -> Located a -> [Expr a] -> Expr a
mkCallOper iv op [e] = ExprLoc (location e) (CallOper iv op [e])
mkCallOper iv op es  = loc sl el (CallOper iv op es)
  where
    sl = location (head es)
    el = location (last es)

mkCallExpr :: IsVectorized -> FuncOrMethod a -> [TypeArgument a] -> [Expr a] -> Location -> Expr a
mkCallExpr iv fom tyArgs args endLoc =
  let bgnLoc = case fom of { Func (Located l _) -> l; Method s _ -> location s } in
  loc bgnLoc endLoc (Call iv fom tyArgs args)

mkDomain :: TypeCon -> Location -> Location -> Type Text
mkDomain con sl el
  | goodCon = TCon con $ joinLocations sl el
  | otherwise = error "ICE: mkDomain bad constructor argument"
  where
    goodCon = con `elem` domainConstructors

mkStage :: TypeCon -> Location -> Location -> Type Text
mkStage con sl el
  | goodCon = TCon con $ joinLocations sl el
  | otherwise = error "ICE: mkStage bad constructor argument"
  where
    goodCon = con `elem` [ConPre, ConPost, ConNoStage]

mkFalse :: Expr Text
mkFalse
  = Lit (ConstBool False)

mkAssertFalse :: Expr Text
mkAssertFalse
  = Call NotVectorized (Func (noLoc "assert")) [] $
    [mkFalse]

mkArrType :: Type Text -> Location -> Location -> Type Text
mkArrType elTy start end =
  TApp (TCon ConArr start) [elTy] $ joinLocations start end

mkListType :: Type Text -> Location -> Location -> Type Text
mkListType elTy start end =
  TApp (TCon ConList start) [elTy] $ joinLocations start end

mkSignature
  :: Located (FuncIdentifier Text)
  -> Located [TypeParam Text]
  -> Located [FuncParam Text]
  -> Type Text
  -> Maybe (Located Fixity)
  -> Located [TypePred Text]
  -> LSignature Text
mkSignature funcId typeParams params returnTy fixity constraints =
  loc (location funcId) (location returnTy) $
  Signature { _sigName = _fiName <$> funcId
            , _sigTypeParameters = typeParams
            , _sigParameters = params
            , _sigConstraints = constraints
            , _sigReturnType = returnTy
            , _sigIsOperator = case unLocated funcId of
                FunctionId{} -> False
                OperatorId{} -> True
            , _sigFixity = fixity
	    , _sigEffect = Nothing
            }

mkExtern :: Bool -> Location -> LSignature Text -> LSignature Text
mkExtern isPub fn sig =
  loc fn (location sig) $ unLocated sig & sigIsPublic .~ isPub

mkFunction :: (Located IsSieveFn , Bool) -> Location -> LSignature Text -> Expr Text -> LFunction Text
mkFunction (Located _ isf , isPub) fn sig body =
  loc fn (location body) $ Function (sig & mapped.sigIsPublic .~ isPub) body isf

mkTypeDef :: Location -> Location -> Located Text -> Bool ->
    Located [TypeParam Text] -> Located Kind -> Located [TypePred Text] ->
    Type Text -> LTypeDef Text
mkTypeDef start end name isPub typeParams kind constraints ty =
  loc start end $
  TypeDef { _tyDefName = name
          , _tyDefIsPublic = isPub
          , _tyDefParams = typeParams
          , _tyDefResultKind = kind
          , _tyDefConstraints = constraints
          , _tyDefType = ty
          }

mkQualifiedType :: Type Text -> Type Text -> Type Text -> Type Text
mkQualifiedType t1 t2 t3 =
    let l = joinLocations (location t1) (joinLocations (location t2) (location t3))
    in mkQualifiedL t1 t2 t3 l

mkProgram :: [TopLevel Text] -> Parser (LProgram Text)
mkProgram ts = do
  let typeDefs = reverse [x | TopTypeDef x <- ts]
  let structDecls = reverse [x | TopStructDecl x <- ts]
  let funs = reverse [x | TopFunction x <- ts]
  let exts = reverse [x | TopExtern x <- ts]
  let imports = reverse [x | TopImport x <- ts]
  let impls = reverse [x | TopStructImpl x <- ts]
  defaults <- case [x | TopDefault x <- ts] of
    []     -> return (noLoc $ Default [])
    d : ds
      | null ds && isMainPresent funs
        -> return d
      | otherwise 
        -> parseError (location d) "More than one default declaration, or default declaration without main function"
  return $ loc firstLoc lastLoc $ Program
    { _programTypeDefs = typeDefs
    , _programStructDecls = structDecls
    , _programTopFunctions = funs
    , _programTopExterns = exts
    , _programImports = imports
    , _programStructImpls = impls
    , _programDefaults = defaults
    }
  where
    (firstLoc, lastLoc) = case ts of
      [] -> (NoLocation, NoLocation)
      _ -> (locF $ last ts, locF $ head ts)
    locF (TopTypeDef x) = location x
    locF (TopFunction x) = location x
    locF (TopExtern x) = location x
    locF (TopImport x) = location x
    locF (TopStructDecl x) = location x
    locF (TopStructImpl x) = location x
    locF (TopDefault x) = location x

mkPredDef :: Location -> Location -> Located Text -> Kind -> Type Text -> TypePred Text
mkPredDef start end var kind ty =
  TypePred PConDef [TVar (unLocated var) kind (location var), ty] $
  joinLocations start end

isMainPresent :: [LFunction Text] -> Bool
isMainPresent
  = elem mainFName . fmap (unLocated . _sigName . unLocated . _funSignature . unLocated)

happyError :: Parser a
happyError = do
  loc <- getParseLocation
  parseError loc "Parse error."

}
