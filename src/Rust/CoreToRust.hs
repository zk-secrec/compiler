{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

-- Translation from Core to Rust.
module Rust.CoreToRust (coreToRust) where

import Basic.Name (mainFName, nameOccName)
import Basic.Var
import Basic.Location (Location, unLocated)
import Core.Syntax
import Rust.SemanticsHelpers hiding (varToString, idToString, funIdToString, idToBaseString)
import Rust.PrimitiveTypes
import qualified Rust.SemanticsHelpers
import Parser.Syntax
import Support.Pretty
import Support.UniqMap (mapUM, findUM)
import Typing.StructEnv
import ConfigurationCheck
import CCC.Syntax (Versioned(..))

import Control.Monad
import Data.Char
import Data.Graph (flattenSCCs)
import Data.IORef
import Data.List
import Data.Maybe
import GHC.Stack (HasCallStack)
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Numeric
import Control.Lens (toListOf)
import System.IO
import GHC.Natural (Natural)
import Text.Printf
import qualified Data.Text as T

-- Removes from identifiers the characters, which Rust 2021 might not like
stringIdToRust :: String -> String
stringIdToRust = filter (\ c -> isAsciiUpper c || isAsciiLower c || isDigit c || c == '_')

charToRust :: Char -> String
charToRust '"' = "\\\""
charToRust '\\' = "\\\\"
charToRust c | isAscii c && isPrint c = [c]
             | otherwise = "\\u{" ++ showHex (ord c) "" ++ "}"

stringLiteralToRust :: String -> String
stringLiteralToRust s = "\"" ++ concatMap charToRust s ++ "\""

varToString :: Var -> String
varToString x | Rust.SemanticsHelpers.idToString x == "scalar" = "()"
              | otherwise = (stringIdToRust . Rust.SemanticsHelpers.varToString) x

idToString :: Id -> String
idToString = stringIdToRust . Rust.SemanticsHelpers.idToString

funIdToString :: Id -> String
funIdToString = stringIdToRust . Rust.SemanticsHelpers.funIdToString

idToBaseString :: Id -> String
idToBaseString = stringIdToRust . Rust.SemanticsHelpers.idToBaseString

operToFun :: String -> String
operToFun "+" = "add"
operToFun "-" = "sub"
operToFun "*" = "mul"
operToFun "/" = "div"
operToFun "%" = "modulo"
operToFun "&" = "and"
operToFun "&&" = "and"
operToFun "|" = "or"
operToFun "||" = "or"
operToFun "^" = "xor"
operToFun "!" = "not"
operToFun "==" = "eq"
operToFun "!=" = "neq"
operToFun "<" = "lt"
operToFun "<=" = "leq"
operToFun ">" = "gt"
operToFun ">=" = "geq"
operToFun f = stringIdToRust f

idOperToFun :: Id -> String
idOperToFun = operToFun . Rust.SemanticsHelpers.idToString

modToNat :: (?ctx :: Context) => ExtendedNatural -> String
modToNat m =
  case Map.lookup m (_natLiteralIndices ?ctx) of
    Nothing -> error "ICE: unexpected Nat literal!"
    Just (index, _) -> "ctx.nat_type_literals[" ++ show index ++ " /* value: " ++ show m ++ " */]"

data Context
  = Ctx
  { _indent :: IORef String
  , _lineFinished :: IORef Bool
  , _literalIndices :: Map Integer (Int, Int)
  , _natLiteralIndices :: Map ExtendedNatural (Int, Int)
  , _strLiteralIndices :: Map String (Int, Int)
  , _numPostModuli :: Int
  , _recursiveVars :: IORef (Set Var)
  , _refArgMap :: IORef (Map Var String) -- maps a temporary variable of a ref argument to its expression in Rust
  , _structsEnv :: StructsEnv
  , _structsWithFinalizer :: IORef (Set Var)
  , _globalFunMap :: Map Var (Int, Int) -- number of type and value arguments of each global function
  , _externSet :: Set Var -- variables corresponding to extern functions
  , _sieveFunSet :: Set Var -- variables corresponding to functions that are translated to SIEVE IR
  , _handle :: Handle
  , _isInsideSieveFn :: Bool -- are we inside a sieve function definition
  }

listElemType :: Type Var -> Type Var
listElemType = \case
  TQualify u _ _ -> listElemType u
  TCast q _ -> listElemType q
  TCastUnqual u _ -> listElemType u
  TList t -> t
  t -> error $ "listElemType: not a list type: " ++ showType t

typeToDomainTypeRust :: (?ctx :: Context) => Type Var -> String
typeToDomainTypeRust = \case
  TDomain TVPublic -> "Public"
  TDomain TVVerifier -> "Verifier"
  TDomain TVProver -> "Prover"
  TVar x KindDomain _ -> varToString x
  TVar x KindStar _ -> varToString x ++ ".domain"
  TGetDomain t -> "(" ++ typeToRust False t ++ ").domain"
  TCastDomain t d -> "tcast_domain(" ++ typeToRust False t ++ ", " ++ typeToDomainTypeRust d ++ ")"
  TQualify _ _ d -> typeToDomainTypeRust d
  t -> error $ "typeToDomainTypeRust: not a domain type: " ++ showType t

typeToStageTypeRust :: (?ctx :: Context) => Type Var -> String
typeToStageTypeRust = \case
  TStage TVPre -> "Pre"
  TStage TVPost -> "Post"
  TVar x KindStage _ -> varToString x
  TGetStage t -> "(" ++ typeToRust False t ++ ").stage"
  TCastStage t d -> "tcast_stage(" ++ typeToRust False t ++ ", " ++ typeToDomainTypeRust d ++ ")"
  TQualify _ s _ -> typeToStageTypeRust s
  _ -> error "typeToStageTypeRust: not a stage type"

typeToRefNatTypeRust :: (?ctx :: Context) => Type Var -> String
typeToRefNatTypeRust = \case
  TNat m -> '&' : modToNat m
  TVar x KindNat _ -> varToString x
  t -> error $ "typeToRefNatTypeRust: not a Nat type " ++ render (pretty t)

typeToNatTypeRust :: (?ctx :: Context) => Type Var -> String
typeToNatTypeRust = \case
  TNat m -> modToNat m ++ ".clone()"
  TVar x KindNat _ -> varToString x ++ ".clone()"
  t -> error $ "typeToNatTypeRust: not a Nat type " ++ render (pretty t)

uintNToRefNatTypeRust :: (?ctx :: Context) => Type Var -> String
uintNToRefNatTypeRust = \case
  TUInt m -> typeToRefNatTypeRust m
  TBool m -> typeToRefNatTypeRust m
  TQualify u _ _ -> uintNToRefNatTypeRust u
  TCast q _ -> uintNToRefNatTypeRust q
  TCastUnqual u _ -> uintNToRefNatTypeRust u
  t -> error $ "uintNToNatTypeRust: not an uint[N] type: " ++ showType t

sizedTypeToRefNatTypesRust :: (?ctx :: Context) => Type Var -> String
sizedTypeToRefNatTypesRust = \case
  TUInt m -> "SoA::Scalar(" ++ typeToRefNatTypeRust m ++ ")"
  TBool m -> "SoA::Scalar(" ++ typeToRefNatTypeRust m ++ ")"
  TUnit -> handle_tuple []
  TQualify u _ _ -> sizedTypeToRefNatTypesRust u
  TCast q _ -> sizedTypeToRefNatTypesRust q
  TCastUnqual u _ -> sizedTypeToRefNatTypesRust u
  TTuple ts -> handle_tuple ts
  TList t -> "SoA::ListType(Box::new(" ++ sizedTypeToRefNatTypesRust t ++ "))" -- used for non-vectorized calls
  t -> case tryGetFieldTypes (_structsEnv ?ctx) t of
    Just ts -> handle_tuple ts
    -- TODO: sizedTypeToRefNatTypesRust can currently be called also for non-Sized types
    -- (for partially applied functions for which it is not known if it is a sieve fn)
    -- so we cannot use error here, instead we return an arbitrary value as it will not be used
    --Nothing -> error $ "sizedTypeToNatTypeRust: not a SizedType: " ++ showType t
    Nothing -> "SoA::Empty"
  where
    handle_tuple ts = "SoA::Tuple(vec![" ++ intercalate ", " (map sizedTypeToRefNatTypesRust ts) ++ "])"

boolToRust :: Bool -> String
boolToRust False = "false"
boolToRust True = "true"

sizedTypeToRefNatTypesOrPrePublicRust :: (?ctx :: Context) => Type Var -> String
sizedTypeToRefNatTypesOrPrePublicRust = sizedTypeToRefNatTypesOrPrePublicRust0 True where
  sizedTypeToRefNatTypesOrPrePublicRust0 :: (?ctx :: Context) => Bool -> Type Var -> String
  sizedTypeToRefNatTypesOrPrePublicRust0 isPrePublic = \case
    TUInt m -> "SoA::Scalar((" ++ typeToRefNatTypeRust m ++ ", " ++ boolToRust isPrePublic ++ "))"
    TBool m -> "SoA::Scalar((" ++ typeToRefNatTypeRust m ++ ", " ++ boolToRust isPrePublic ++ "))"
    TUnit -> handle_tuple []
    TQualify u (TStage TVPre) (TDomain TVPublic) -> sizedTypeToRefNatTypesOrPrePublicRust0 isPrePublic u
    TQualify u _ _ -> sizedTypeToRefNatTypesOrPrePublicRust0 False u
    TCast q _ -> sizedTypeToRefNatTypesOrPrePublicRust0 False q
    TCastUnqual u _ -> sizedTypeToRefNatTypesOrPrePublicRust0 False u
    TTuple ts -> handle_tuple ts
    TList t -> "SoA::ListType(Box::new(" ++ sizedTypeToRefNatTypesOrPrePublicRust0 isPrePublic t ++ "))" -- used for non-vectorized calls
    t -> case tryGetFieldTypes (_structsEnv ?ctx) t of
      Just ts -> handle_tuple ts
      -- TODO: sizedTypeToRefNatTypesRust can currently be called also for non-Sized types
      -- (for partially applied functions for which it is not known if it is a sieve fn)
      -- so we cannot use error here, instead we return an arbitrary value as it will not be used
      --Nothing -> error $ "sizedTypeToNatTypeRust: not a SizedType: " ++ showType t
      Nothing -> "SoA::Empty"
    where
      handle_tuple ts = "SoA::Tuple(vec![" ++ intercalate ", " (map (sizedTypeToRefNatTypesOrPrePublicRust0 isPrePublic) ts) ++ "])"

addLifetimes :: String -> String
addLifetimes = f where
  f "" = ""
  f ('&' : s) = "&'a " ++ f s
  f (c : s) = c : f s

storeToRefNatTypeRust :: (?ctx :: Context) => Type Var -> String
storeToRefNatTypeRust = \case
  TStore k v ->
    let
      m1 = uintNToRefNatTypeRust k
      m2 = uintNToRefNatTypeRust v
    in
      if m1 == m2 then m1 else error "storeToNatTypeRust: stores with different moduli for keys and values not supported"
  TQualify u _ _ -> storeToRefNatTypeRust u
  t -> error $ "storeToRefNatTypeRust: not a store type: " ++ showType t

typeToValueTypeRust :: (?ctx :: Context) => Type Var -> String
typeToValueTypeRust (TCastUnqual u d) = "tcast_unqual(stack, " ++ typeToValueTypeRust u ++ ", " ++ typeToDomainTypeRust d ++ ")"
typeToValueTypeRust t = "&" ++ typeToValueTypeRepRust t

typeToValueTypeRepRust :: (?ctx :: Context) => Type Var -> String
typeToValueTypeRepRust = \case
  TUnit -> "TUnit"
  TBool m -> "TBool(" ++ typeToRefNatTypeRust m ++ ")"
  TUInt m -> "TUInt(" ++ typeToRefNatTypeRust m ++ ")"
  TList t -> "TList(" ++ typeToValueTypeRust t ++ ")"
  TArr t -> "TArr(" ++ typeToValueTypeRust t ++ ")"
  TTuple ts -> handle_tuple ts
  TStore k v -> "TStore(" ++ typeToValueTypeRust k ++ ", " ++ typeToValueTypeRust v ++ ")"
  TQualify u s d -> "TQualify(" ++ typeToValueTypeRust u ++ ", " ++ typeToStageTypeRust s ++ ", " ++ typeToDomainTypeRust d ++ ")"
  t -> case tryGetFieldTypes (_structsEnv ?ctx) t of
    Just ts -> handle_tuple ts
    Nothing -> error $ "typeToValueTypeRust: unsupported type: " ++ showType t
  where
    handle_tuple ts = "TTuple(&[" ++ intercalate ", " (map typeToValueTypeRust ts) ++ "])"

-- This and typeToRust ignore value types inside qualified types.
-- Use typeToValueTypeRust to include value types in qualified types (using TQualify instead of QualifiedType).
typeToQualifiedTypeRust :: (?ctx :: Context) => Type Var -> String
typeToQualifiedTypeRust = \case
  TQualify _ s d -> "QualifiedType{stage: " ++ typeToStageTypeRust s ++ ", domain: " ++ typeToDomainTypeRust d ++ "}"
  TCast t d -> "tcast(" ++ typeToRust False t ++ ", " ++ typeToDomainTypeRust d ++ ")"
  TVar x KindStar _ -> varToString x
  t -> error "typeToQualifiedTypeRust: not a qualified type: " ++ render (pretty t)

-- Translate stage, domain, qualified, and nat types to Rust.
-- needRef specifies if a reference is needed instead of ownership.
-- needRef is ignored for stage, domain, and qualified types, as these are always passed by value.
-- Currently not implemented for unqualified types;
-- needRef would need to be used for unqualified types.
typeToRust :: (?ctx :: Context) => Bool -> Type Var -> String
typeToRust needRef = \case
  t -> case typeKind t of
    KindStage -> typeToStageTypeRust t
    KindDomain -> typeToDomainTypeRust t
    KindStar -> typeToQualifiedTypeRust t
    KindNat -> if needRef then typeToRefNatTypeRust t else typeToNatTypeRust t
    KindUnqualified -> error "typeToRust should not be called for unqualified types"
    k -> error $ "typeToRust unimplemented for " ++ render (pretty t) ++ " of kind " ++ render (pretty k)

getTypeArgDecls :: (?ctx :: Context) => [Type Var] -> [String]
getTypeArgDecls ts =
  let
    getTypeArgDecl t | isKindPassed (typeKind t) = Just (typeToRust True t)
                     | otherwise = Nothing
  in
    mapMaybe getTypeArgDecl ts

getHofTypeArgDecls :: (?ctx :: Context) => [Type Var] -> [String]
getHofTypeArgDecls ts =
  let
    getHofTypeArgDecl t =
      let
        t_rust = typeToRust False t
      in
        case typeKind t of
          KindNat -> Just ("TENat(" ++ t_rust ++ ")")
          KindStage -> Just ("TEStage(" ++ t_rust ++ ")")
          KindDomain -> Just ("TEDomain(" ++ t_rust ++ ")")
          KindStar -> Just ("TEQualified(" ++ t_rust ++ ")")
          _ -> Nothing
  in
    mapMaybe getHofTypeArgDecl ts

writeLine :: Context -> String -> IO ()
writeLine Ctx{..} s = do
  indent <- readIORef _indent
  lineFinished <- readIORef _lineFinished
  hPutStrLn _handle $ if lineFinished then indent ++ s else s
  writeIORef _lineFinished True

writeUnfinishedLine :: Context -> String -> IO ()
writeUnfinishedLine Ctx{..} s = do
  indent <- readIORef _indent
  lineFinished <- readIORef _lineFinished
  hPutStr _handle $ if lineFinished then indent ++ s else s
  writeIORef _lineFinished False

increaseIndent :: Context -> IO ()
increaseIndent Ctx{..} =
  modifyIORef' _indent ("    " ++)

decreaseIndent :: Context -> IO ()
decreaseIndent Ctx{..} =
  modifyIORef' _indent (drop 4)

withIncreasedIndent :: Context -> IO () -> IO ()
withIncreasedIndent ctx act = do
  increaseIndent ctx
  act
  decreaseIndent ctx

-- are type variables of this kind passed as function arguments is the generated Rust code
isKindPassed :: Kind -> Bool
isKindPassed KindNat = True
isKindPassed KindDomain = True
isKindPassed KindStage = True
isKindPassed KindStar = True
isKindPassed _ = False

-- version of last with stacktrace when failing, for easier debugging
last' :: HasCallStack => [a] -> a
last' [] = error "last': empty list"
last' xs = last xs

isStoreAccess :: [CoreOffset] -> Bool
isStoreAccess offsets = not (null offsets) && case last' offsets of COffKey _ -> True; _ -> False

translateOffsets0 :: String -> [CoreOffset] -> String
translateOffsets0 x [] = x
translateOffsets0 x (off:offs) =
  let
    x' = translateOffsets0 x offs
  in
    case off of
      COffStruct i ->
        "&index_struct(ctx, " ++ x' ++ ", " ++ show i ++ ")"
      COffTuple i ->
        "&index_struct(ctx, " ++ x' ++ ", " ++ show i ++ ")"
      COffDynamic (ArrayIndex x1) ->
        "&index_array(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
      COffDynamic (ArrayFromTo x1 x2) ->
        "&slice_array(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ", " ++ varToString x2 ++ ")"
      COffDynamic (ArrayTo x2) ->
        "&slice_array_to(ctx, " ++ x' ++ ", " ++ varToString x2 ++ ")"
      COffDynamic (ArrayFrom x1) ->
        "&slice_array_from(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
      COffDynamic ArrayAll ->
        "&slice_array_all(ctx, " ++ x' ++ ")"
      _ -> error "Unsupported CoreOffset"

translateOffsets :: (?ctx :: Context) => Type Var -> String -> [CoreOffset] -> String
translateOffsets retType x offs =
  case reverse offs of
    [] -> x
    off : offs ->
      let
        x' = translateOffsets0 x offs
        d = typeToDomainTypeRust retType
      in
        case off of
          COffStruct i ->
            valueToPrimitiveIfNecessary retType $ "&index_struct(ctx, " ++ x' ++ ", " ++ show i ++ ")"
          COffTuple i ->
            valueToPrimitiveIfNecessary retType $ "&index_struct(ctx, " ++ x' ++ ", " ++ show i ++ ")"
          COffDynamic (ArrayIndex x1)
            | isTypePrimitive retType -> "index_array_" ++ primitiveToRustType retType ++ "(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
            | otherwise -> "&index_array_polymorphic" ++ "(ctx, " ++ d ++ ", " ++ x' ++ ", " ++ varToString x1 ++ ")"
          COffDynamic (ArrayFromTo x1 x2) ->
            "&slice_array(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ", " ++ varToString x2 ++ ")"
          COffDynamic (ArrayTo x2) ->
            "&slice_array_to(ctx, " ++ x' ++ ", " ++ varToString x2 ++ ")"
          COffDynamic (ArrayFrom x1) ->
            "&slice_array_from(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
          _ -> error "Unsupported CoreOffset"

translateOffsetsMut0 :: String -> [CoreOffset] -> String
translateOffsetsMut0 x [] = x
translateOffsetsMut0 x (off:offs) =
  let
    x' = translateOffsetsMut0 x offs
  in
    case off of
      COffStruct i ->
        "index_struct_mut(ctx, " ++ x' ++ ", " ++ show i ++ ")"
      COffTuple i ->
        "index_struct_mut(ctx, " ++ x' ++ ", " ++ show i ++ ")"
      COffDynamic (ArrayIndex x1) ->
        "index_array_mut(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
      COffDynamic _ ->
        error "Mutable slices are not supported"
      _ -> error "Unsupported CoreOffset"


translateOffsetsMut :: String -> [CoreOffset] -> String
translateOffsetsMut x offs = translateOffsetsMut0 x (reverse offs)

assignToMutable :: String -> String -> String
assignToMutable x y = "assign_to_mutable(ctx, " ++ x ++ ", " ++ y ++ ")"

translateOffsetsRef :: (?ctx :: Context) => Var -> [CoreOffset] -> Type Var -> String
translateOffsetsRef x offs retType =
  case reverse offs of
    [] -> varToString x
    off : offs ->
      let
        x' = translateOffsetsMut0 (varToString x) offs
      in
        case off of
          COffStruct i ->
            "index_struct_mut(ctx, " ++ x' ++ ", " ++ show i ++ ")" ++ (if isTypePrimitive retType then ".into()" else "")
          COffTuple i ->
            "index_struct_mut(ctx, " ++ x' ++ ", " ++ show i ++ ")" ++ (if isTypePrimitive retType then ".into()" else "")
          COffDynamic (ArrayIndex x1)
            | isTypePrimitive retType -> "index_array_mut_" ++ primitiveToRustType retType ++ "(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
            | otherwise -> "index_array_mut(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ")"
          COffDynamic _ ->
            error "Mutable slices are not supported"
          _ -> error "Unsupported CoreOffset"

translateOffsetsAssign :: (?ctx :: Context) => Var -> [CoreOffset] -> Var -> String
translateOffsetsAssign x offs y =
  case reverse offs of
    [] -> assignToMutable (varToString x) (varToString y)
    off : offs ->
      let
        x' = translateOffsetsMut0 (varToString x) offs
        t = idToType y
        d = typeToDomainTypeRust t
      in
        case off of
          COffStruct i ->
            assignToMutable ("index_struct_mut(ctx, " ++ x' ++ ", " ++ show i ++ ")") (varToBorrowedValue y)
          COffTuple i ->
            assignToMutable ("index_struct_mut(ctx, " ++ x' ++ ", " ++ show i ++ ")") (varToBorrowedValue y)
          COffDynamic (ArrayIndex x1)
            | isTypePrimitive t -> "index_array_assign_" ++ primitiveToRustType t ++ "(ctx, " ++ d ++ ", " ++ x' ++ ", " ++ varToString x1 ++ ", " ++ varToString y ++ ")"
            | otherwise -> "index_array_assign" ++ "(ctx, " ++ x' ++ ", " ++ varToString x1 ++ ", " ++ varToString y ++ ")"
          COffDynamic _ ->
            error "Mutable slices are not supported"
          _ -> error "Unsupported CoreOffset"

translateOffsetsPrimitiveMut0 :: String -> [CoreOffset] -> String
translateOffsetsPrimitiveMut0 x [] = x
translateOffsetsPrimitiveMut0 _ _ = error "translateOffsetsPrimitiveMut"

translateOffsetsPrimitiveMut :: String -> [CoreOffset] -> String
translateOffsetsPrimitiveMut x offs = translateOffsetsPrimitiveMut0 x (reverse offs)

translateRecArrOffsets :: (?ctx :: Context) => Type Var -> Type Var -> String -> [CoreOffset] -> String
translateRecArrOffsets arrType retType x (COffDynamic (ArrayIndex x1) : offs) =
    let
      x' = if isTypePrimitive (listElemType arrType)
             then x ++ "[" ++ varToString x1 ++ " as usize]"
             else "&index_vector(ctx, &" ++ x ++ ", " ++ varToString x1 ++ ")"
    in
      translateOffsets retType x' offs
translateRecArrOffsets _ _ _ _ = error "translateRecArrOffsets"

translateIfThenElse :: Context -> Var -> String -> CoreLet -> CoreLet -> IO ()
translateIfThenElse ctx recRetVar cond e1 e2 = do
  writeLine ctx $ "if " ++ cond ++ " {"
  translateLetWithTypeChange ctx (idToType recRetVar) e1
  writeLine ctx "} else {"
  translateLetWithTypeChange ctx (idToType recRetVar) e2
  writeUnfinishedLine ctx "}"

translateDebugMcl :: Context -> Maybe CoreLet -> IO ()
translateDebugMcl ctx Nothing = writeUnfinishedLine ctx $ "\"\""
translateDebugMcl ctx (Just e) = do
  writeLine ctx $ "get_vstr(&{"
  withIncreasedIndent ctx $ translateLet ctx e
  writeUnfinishedLine ctx $ "})"

primitiveToValue :: (?ctx :: Context) => Type TyVar -> String -> String
primitiveToValue t x = primitiveToValue0 t ++ "(ctx, " ++ typeToDomainTypeRust t ++ ", " ++ x ++ ")"

primitiveVarToValue :: (?ctx :: Context) => Var -> String
primitiveVarToValue x = primitiveToValue (idToType x) (varToString x)

-- replace the domaintype with another string, needed in *_hof functions, where the type variable is not available directly
primitiveToValueD :: (?ctx :: Context) => String -> Type TyVar -> String -> String
primitiveToValueD d t x = primitiveToValue0 t ++ "(ctx, " ++ d ++ ", " ++ x ++ ")"

-- convert primitive types to Value and clone &Value to Value
varToClonedValue :: (?ctx :: Context) => Var -> String
varToClonedValue x = if isTypePrimitive (idToType x) then primitiveVarToValue x else varToString x ++ ".clone()"

-- convert primitive types to &Value and leave &Value as is
varToBorrowedValue :: (?ctx :: Context) => Var -> String
varToBorrowedValue x = if isTypePrimitive (idToType x) then '&' : primitiveVarToValue x else varToString x

valueToPrimitive :: Type TyVar -> String -> String
valueToPrimitive t x = valueToPrimitive0 t ++ "(" ++ x ++ ")"

valueToPrimitiveIfNecessary :: Type TyVar -> String -> String
valueToPrimitiveIfNecessary t x = if isTypePrimitive t then valueToPrimitive t x else x

valueToExternIfNecessary :: Type TyVar -> String -> String
valueToExternIfNecessary t x = if isTypePrimitive t then valueToPrimitive t x else (if isNonPrimitiveExtern t then "(" ++ x ++ ").into()" else x)

-- TODO: Currently just commented out the non-emp behavior.
translateLit :: Context -> Type TyVar -> Constant -> String
translateLit ctx@Ctx{..} t = \case
  ConstUnit -> "()"
  ConstInt i
    | isTypePrimitive t -> show i ++ primitiveToRustType t
    | otherwise -> case Map.lookup i _literalIndices of
        Nothing -> error "ICE: Unseed integer literal."
        Just (index, _) ->
            "&int_literal(ctx, " ++ natType ++ ", " ++  show index ++ " /* value: " ++ show i ++ " */)"
  ConstBool b
    | isTypePrimitive t -> if b then "true" else "false"
    | otherwise -> "&rep::Bool::new(" ++ (if b then "true" else "false") ++ ")"
  ConstString s -> case Map.lookup s _strLiteralIndices of
    Nothing -> "&rep::Str::new(String::from(" ++ stringLiteralToRust s ++ "))"
    Just (index, _) -> "&ctx.string_literals[" ++ show index ++ " /* value: " ++ show s ++ " */]"
  where
    natType = let ?ctx = ctx in uintNToRefNatTypeRust t

translateDomainCast :: (?ctx :: Context) => Var -> Type TyVar -> String
translateDomainCast x t | isTypePrimitive (idToType x) = varToString x
                        | otherwise = "&cast_to_domain(ctx, " ++ typeToDomainTypeRust t ++ ", " ++ varToString x ++ ")"

isUnitArgFunc :: Type TyVar -> Bool
isUnitArgFunc t =
  let
    (args, _) = splitFuncType t
  in
    case args of
      [arg] -> isUnitType arg
      _ -> False

domainCheck :: String -> String
domainCheck d = if d == "Public" then "true" else d ++ " == Public || (" ++ d ++ " <= CURR_DOMAIN && !ctx.inside_sieve_fn_def())"

translateExpr :: Context -> Var -> CoreExpr -> IO ()
translateExpr ctx@Ctx{..} recRetVar e = case e of
  CeLit lit -> do
    let t = idToType recRetVar
    writeUnfinishedLine ctx $ translateLit ctx t lit
  CeVar x
    | isTypePrimitive (idToType recRetVar) && not (isTypePrimitive (idToType x)) ->
        writeUnfinishedLine ctx $ valueToPrimitive (idToType recRetVar) $ varToString x
    | otherwise -> writeUnfinishedLine ctx $ varToString x
  CeCast x t ->
    let ?ctx = ctx in
    let
      inType = idToType x
      t' = idToType recRetVar
    in writeUnfinishedLine ctx $
      case t of
        TDomain _ -> translateDomainCast x t
        TVar _ KindDomain _ -> translateDomainCast x t
        TStage TVPost -> varToString x
        TStage TVPre
          | isTypePrimitive inType -> varToString x
          | otherwise -> valueToPrimitiveIfNecessary t' $ "cast_to_pre(" ++ varToString x ++ ")"
        TBool t ->
          case (isTypePrimitive inType, isTypePrimitive t') of
            (True, True) -> varToString x ++ " as " ++ primitiveToRustType t'
            (True, False) ->
                "&cast_to_bool(ctx," ++ uintNToRefNatTypeRust inType ++ ", &" ++ primitiveVarToValue x ++ ", " ++ typeToRefNatTypeRust t ++ ")"
            (False, True) ->
                valueToPrimitive t' ("&cast_to_bool(ctx," ++ uintNToRefNatTypeRust inType ++ ", " ++ varToString x ++ ", " ++ typeToRefNatTypeRust t ++ ")")
            (False, False) ->
                "&cast_to_bool(ctx," ++ uintNToRefNatTypeRust inType ++ ", " ++ varToString x ++ ", " ++ typeToRefNatTypeRust t ++ ")"
        TUInt t ->
          case (isTypePrimitive inType, isTypePrimitive t') of
            (True, True) -> varToString x ++ " as " ++ primitiveToRustType t'
            (True, False) ->
                "&cast_to_uint(ctx," ++ uintNToRefNatTypeRust inType ++ ", &" ++ primitiveVarToValue x ++ ", " ++ typeToRefNatTypeRust t ++ ")"
            (False, True) ->
                valueToPrimitive t' ("&cast_to_uint(ctx," ++ uintNToRefNatTypeRust inType ++ ", " ++ varToString x ++ ", " ++ typeToRefNatTypeRust t ++ ")")
            (False, False) ->
                "&cast_to_uint(ctx," ++ uintNToRefNatTypeRust inType ++ ", " ++ varToString x ++ ", " ++ typeToRefNatTypeRust t ++ ")"
        _ -> error $ "translateExpr: Unsupported cast: " ++ showCoreExpr e
  CeTypeToExpr t ->
    writeUnfinishedLine ctx $ "&type_to_expr(" ++ typeToRefNatTypeRust t ++ ")"
  CeTuple xs ->
    writeUnfinishedLine ctx $
      "&StructInner::new_tuple(Box::new([" ++ intercalate ", " (map varToClonedValue xs) ++ "]))"
  CeStructCtor s ts xs -> do
    structsWithFinalizer <- readIORef _structsWithFinalizer
    let typeArgDecls = getTypeArgDecls ts
    let finalizerStr = if Set.member s structsWithFinalizer then "struct_" ++ idToBaseString s ++ "::get_finalizer(ctx" ++ concatMap (", " ++) typeArgDecls ++ ")" else "None"
    writeUnfinishedLine ctx $
      "&StructInner::new(Box::new([" ++ intercalate ", " (map varToClonedValue xs) ++ "]), " ++ finalizerStr ++ ")"
  CeList (ListElems xs) -> do
    let d = typeToDomainTypeRust $ idToType recRetVar
    let elemType = listElemType (idToType recRetVar)
    writeUnfinishedLine ctx $
      if isTypePrimitive elemType
        then "&create_array_" ++ primitiveToRustType elemType ++ "(ctx, " ++ d ++ ", vec![" ++ intercalate ", " (map varToString xs) ++ "])"
        else "&create_array(ctx, " ++ d ++ ", vec![" ++ intercalate ", " (map (\ x -> varToString x ++ ".clone()") xs) ++ "])"
  CeList (ListRange x1 x2) -> do
    let d = typeToDomainTypeRust $ idToType recRetVar
    let elemType = listElemType (idToType recRetVar)
    writeUnfinishedLine ctx $
      if isTypePrimitive elemType
        then "&range_array_" ++ primitiveToRustType elemType ++ "(ctx, " ++ d ++ ", " ++ varToString x1 ++ ", " ++ varToString x2 ++ ")"
        else "&range_array(ctx, " ++ d ++ ", " ++ varToString x1 ++ ", " ++ varToString x2 ++ ")"
  CeList (ListReplicate x1 x2) -> do
    let d = typeToDomainTypeRust $ idToType recRetVar
    let elemType = listElemType (idToType recRetVar)
    writeUnfinishedLine ctx $
      if isTypePrimitive elemType
        then "&replicated_array_" ++ primitiveToRustType elemType ++ "(ctx, " ++ d ++ ", " ++ varToString x1 ++ ", " ++ varToString x2 ++ ")"
        else "&replicated_array(ctx, " ++ d ++ ", " ++ varToString x1 ++ ", " ++ varToString x2 ++ ")"
  CeStoreCtor assocs -> do
    let t = idToType recRetVar
    let d = typeToDomainTypeRust t
    let s = typeToStageTypeRust t
    let m = storeToRefNatTypeRust t
    writeUnfinishedLine ctx $ "&create_store(ctx, " ++ m ++ ", " ++ s ++ ", " ++ d ++  ", &[" ++ intercalate ", " (map (\ (k,v) -> "(" ++ varToString k ++ ", " ++ varToString v ++ ")") assocs) ++ "])"
  CeLoad x offsets0 -> do
    let storeAccess = isStoreAccess offsets0
    let (offsets, ~(COffKey storeKey)) = if storeAccess then (init offsets0, last' offsets0) else (offsets0, undefined)
    recursiveVars <- readIORef _recursiveVars
    let primitiveMutable = idIsMutable x && isTypePrimitive (idToType x)
    let mutable = idIsMutable x && not primitiveMutable && not (isTypePrimitive (idToType recRetVar)) && not storeAccess -- stores are handled differently from other mutable variables
    when mutable $ writeUnfinishedLine ctx $ "&mutable_to_immutable(ctx, "
    let x' = varToString x
    when storeAccess $ writeUnfinishedLine ctx "&read_store(ctx, "
    let recursive = Set.member x recursiveVars
    let arrType = idToType x
    let retType = idToType recRetVar
    writeUnfinishedLine ctx $ (if recursive then translateRecArrOffsets arrType else translateOffsets) retType x' offsets
    when mutable $ writeUnfinishedLine ctx $ ")"
    when storeAccess $ writeUnfinishedLine ctx $ ", " ++ varToString storeKey ++ ")"
  CeRef x offsets -> do
    let x' = translateOffsetsRef x offsets (idToType recRetVar)
    let x'' = if isTypePrimitive (idToType x) then "&mut " ++ x' else x'
    modifyIORef _refArgMap $ Map.insert recRetVar x''
  CeStore x offsets0 y
    | isStoreAccess offsets0 -> do
      let offsets = init offsets0
      let x' = translateOffsetsMut (varToString x) offsets
      let COffKey storeKey = last' offsets0
      writeUnfinishedLine ctx $ "write_store(ctx, " ++ x' ++ ", " ++ varToString storeKey ++ ", " ++ varToString y ++ ")"
    | isTypePrimitive (idToType x) -> do
      let x' = translateOffsetsPrimitiveMut (varToString x) offsets0
      writeUnfinishedLine ctx $ x' ++ " = " ++ varToString y
    | otherwise -> do
      writeUnfinishedLine ctx $ translateOffsetsAssign x offsets0 y
  CeLet e -> do
    writeLine ctx $ (if isTypePrimitive (idToType recRetVar) then "" else "&") ++ "{"
    translateLet ctx e
    writeUnfinishedLine ctx "}"
  CeWire xlen e -> do
    writeLine ctx "&{"
    translateWireExpr ctx xlen e
    writeUnfinishedLine ctx "}"
  CeIfThenElse x0 e1 e2 -> do
    let t = idToType x0
    let d = typeToDomainTypeRust t
    let rt = idToType recRetVar
    let isRetPrim = isTypePrimitive rt
    let cond = varToString x0
    writeLine ctx $ (if isRetPrim then "" else "&") ++ "if " ++ domainCheck d ++ " {"
    increaseIndent ctx
    translateIfThenElse ctx recRetVar cond e1 e2
    writeLine ctx ""
    decreaseIndent ctx
    if isRetPrim
      then writeUnfinishedLine ctx $ "} else { " ++ unknownPrimitive rt ++ " }"
      else writeUnfinishedLine ctx "} else { ctx.unknown.clone() }"
  CeTypeIf p e1 e2 ->
    let
      rt = idToType recRetVar
      isRetPrim = isTypePrimitive rt
      cond =
        case p of
          PredSub lhs rhs _ ->
            let
              lhs' = typeToDomainTypeRust lhs
              rhs' = typeToDomainTypeRust rhs
            in
              lhs' ++ " <= " ++ rhs'
          PredPre s _ ->
            typeToStageTypeRust s ++ " == Pre"
          PredPost s _ ->
            typeToStageTypeRust s ++ " == Post"
          PredField n _ -> "pred_field(ctx, "  ++ typeToRefNatTypeRust n ++ ")"
          PredChallenge n _ -> "pred_challenge(ctx, "  ++ typeToRefNatTypeRust n ++ ")"
          PredConvertible n1 n2 _ -> "pred_convertible(ctx, "  ++ typeToRefNatTypeRust n1 ++ ", " ++ typeToRefNatTypeRust n2 ++ ")"
          PredVectorization _ -> "ctx.is_iter_available"
          PredExtendedArithmetic _ -> "plugin_supported(ctx, \"extended_arithmetic\")"
          PredPermutationCheck _ -> "plugin_supported(ctx, \"permutation_check\")"
          PredVectors _ -> "plugin_supported(ctx, \"vectors\")"
          PredObliviousChoice _ -> "plugin_supported(ctx, \"vectors\")"
          _ -> error ("Unsupported type predicate " ++ render (pretty p))
    in do
      unless isRetPrim $ writeUnfinishedLine ctx "&"
      translateIfThenElse ctx recRetVar cond e1 e2
  CeLoop (CoreForExpr x0 x1 x2 (CoreLet binds [retVar])) -> do
    let t = idToType x0
    let d = typeToDomainTypeRust t
    let x = varToString x0
    let n1 = varToString x1
    let n2 = varToString x2
    let tmpArr = varToString recRetVar
    let elemType = idToType retVar
    let isBoxedArr = isTypePrimitive elemType
    writeLine ctx $ "&if " ++ domainCheck d ++ " {"
    increaseIndent ctx
    writeLine ctx $ "let mut " ++ tmpArr ++ (if isBoxedArr then ": Vec<" ++ primitiveToRustType elemType ++ ">" else "") ++ " = Vec::new();"
    writeLine ctx $ tmpArr ++ ".reserve((" ++ n2 ++ " - " ++ n1 ++ ") as usize);"
    writeLine ctx $ "for " ++ x ++ " in " ++ n1 ++ " .. " ++ n2 ++ " {"
    increaseIndent ctx
    forM_ binds (translateBind ctx)
    writeLine ctx $ tmpArr ++ ".push(" ++ varToString retVar ++ (if isBoxedArr then "" else ".clone()") ++ ");"
    decreaseIndent ctx
    writeLine ctx "}"
    writeLine ctx $
      if isBoxedArr
        then "create_array_" ++ primitiveToRustType elemType ++ "(ctx, Public, " ++ tmpArr ++ ")"
        else "rep::Array::new(" ++ tmpArr ++ ")"
    decreaseIndent ctx
    writeUnfinishedLine ctx "} else { ctx.unknown.clone() }"
  CeLoop (CoreForRange x0 x1 x2 (CoreLet binds _)) -> do
    let t = idToType x0
    let d = typeToDomainTypeRust t
    let x = varToString x0
    writeLine ctx $ "if " ++ domainCheck d ++ " {"
    increaseIndent ctx
    writeLine ctx $ "for " ++ x ++ " in " ++ varToString x1 ++ " .. " ++ varToString x2 ++ " {"
    increaseIndent ctx
    forM_ binds (translateBind ctx)
    decreaseIndent ctx
    writeLine ctx "}"
    decreaseIndent ctx
    writeUnfinishedLine ctx "}"
  CeLoop (CoreForever (CoreLet binds _)) -> do
    writeLine ctx $ "loop {"
    increaseIndent ctx
    forM_ binds (translateBind ctx)
    decreaseIndent ctx
    writeUnfinishedLine ctx "}"
  CeBreak 1 -> do
    writeUnfinishedLine ctx $ "break"
  CeContinue 1 -> do
    writeUnfinishedLine ctx $ "continue"
  CeCall IsVectorized f ts xs _loc -> do
    let fname = idOperToFun f
    let argDecls = map varToString xs
    let hof_argDecls = map (++ ".clone()") argDecls
    when _isInsideSieveFn $ error $ "Vectorized calls are not allowed inside sieve functions (" ++ fname ++ " was called vectorized)"
    let isSieve = Set.member f _sieveFunSet || isBuiltinVar f && fname `elem` ["add", "mul", "sub", "assert_zero"]
    let sieveFn = if isSieve then "Some(" ++ show fname ++ ".to_string())" else "None"
    let numArgs = length xs
    let (argTypes, resType) = splitFuncTypeN (idToType f) numArgs
    let ?ctx = ctx in do
      let outputModuli = sizedTypeToRefNatTypesRust resType
      let inputModuli = map sizedTypeToRefNatTypesRust argTypes
      let typeArgDecls = getTypeArgDecls ts
      let hofTypeArgDecls = getHofTypeArgDecls ts
      if Map.member f _globalFunMap || isBuiltinVar f then
        writeUnfinishedLine ctx $
            "&zip(ctx, stack, " ++ fname ++ "_moduli(ctx" ++ concatMap (", " ++) typeArgDecls ++ "), vec![" ++
            intercalate ", " hofTypeArgDecls ++ "], vec![" ++ intercalate ", " hof_argDecls ++ "], " ++ sieveFn ++ ", " ++ fname ++ "_hof)"
      else
        writeUnfinishedLine ctx $
            "&zip_hof(ctx, stack, " ++ outputModuli ++ ", vec![" ++ intercalate ", " inputModuli ++ "], vec![" ++
            intercalate ", " hof_argDecls ++ "], " ++ fname ++ ")"
  CeCall NotVectorized f ts xs loc -> do
    let
      typeArgDecls = getTypeArgDecls ts
      hof_typeArgDecls = getHofTypeArgDecls ts
    let isExtern = Set.member f _externSet
    let fname = if isExtern then idToBaseString f else idOperToFun f
    let numArgs = length xs
    let numArgs' = if numArgs == 0 && isUnitArgFunc (idToType f) then 1 else numArgs
    -- argument and result types with type variables not replaced
    let (argTypesF, _) = splitFuncTypeN (idToType f) numArgs
    let (_, resTypeF) = splitFuncTypeN (idToType f) numArgs'
    let is_primitive_builtin = isBuiltinVar f && (fname `elem` ["add", "sub", "mul", "div", "modulo", "and", "or", "xor", "not", "eq", "neq", "lt", "leq", "gt", "geq"]) && isTypePrimitive (idToType (head xs))
    let argDecls = map varToString xs
    non_hof_argDecls <- forM (zip xs argTypesF) $ \ (x, tF) -> do
      m <- readIORef _refArgMap
      s <- case Map.lookup x m of
             Just s -> do
               writeIORef _refArgMap $ Map.delete x m
               return s
             Nothing -> return $ varToString x
      if | not is_primitive_builtin && isTypePrimitive (idToType x) && not (isTypePrimitive tF) -> return $ '&' : primitiveVarToValue x
         | isExtern && isNonPrimitiveExtern (idToType x) -> return $ "(" ++ s ++ ").into()"
         | otherwise -> return s
    let
      hof_argDecls =
        flip map xs $ \ x ->
          if isTypePrimitive (idToType x)
            then primitiveVarToValue x
            else varToString x ++ ".clone()"
    -- if a sieve function is called from an another sieve function then the former is inlined as if it were a non-sieve function
    let isSieve = Set.member f _sieveFunSet && not _isInsideSieveFn
    -- For some reason, this does not work:
    --let numArgs = length xs
    --let (_argTypes, resType) = splitFuncTypeN (idToType f) numArgs
    --let inputModuli = map sizedTypeToRefNatTypesRust argTypes
    let inputModuli = flip map xs $ \ x -> sizedTypeToRefNatTypesOrPrePublicRust (idToType x)
    let resType = idToType recRetVar
    let outputModuli = sizedTypeToRefNatTypesRust resType
    let extraTypeArgDecls | fname `elem` ["get_public", "get_instance", "get_witness", "array_to_post", "freeze", "thaw", "to_string"] && not (null ts) = [typeToValueTypeRust (head ts)]
                          | fname == "assert_eq" && length ts >= 3 = [typeToValueTypeRust (ts !! 1), typeToValueTypeRust (ts !! 2)]
                          | otherwise = []
    let extraStackArgs = ["&mut stack.scope()" | not (isBuiltinVar f) || fname == "array_to_post"]
    let non_hof_call = writeUnfinishedLine ctx $ fname ++ "(ctx" ++ concatMap (", " ++) (extraStackArgs ++ extraTypeArgDecls ++ typeArgDecls ++ non_hof_argDecls) ++ ")" ++
                                                          (if isExtern && isNonPrimitiveExtern resType then ".into()" else "")
    let checkDomain s = "if " ++ domainCheck (typeToDomainTypeRust (ts !! 1)) ++ " { " ++ s ++ " } else { 0 }"
    let
      primitive_builtin_call = writeUnfinishedLine ctx $
        case fname of
          "add" -> non_hof_argDecls !! 0 ++ ".wrapping_add(" ++ non_hof_argDecls !! 1 ++ ")"
          "sub" -> non_hof_argDecls !! 0 ++ ".wrapping_sub(" ++ non_hof_argDecls !! 1 ++ ")"
          "mul" -> non_hof_argDecls !! 0 ++ ".wrapping_mul(" ++ non_hof_argDecls !! 1 ++ ")"
          "div" -> checkDomain $ non_hof_argDecls !! 0 ++ " / " ++ non_hof_argDecls !! 1
          "modulo" -> checkDomain $ non_hof_argDecls !! 0 ++ " % " ++ non_hof_argDecls !! 1
          "and" -> non_hof_argDecls !! 0 ++ " && " ++ non_hof_argDecls !! 1
          "or" -> non_hof_argDecls !! 0 ++ " || " ++ non_hof_argDecls !! 1
          "xor" -> non_hof_argDecls !! 0 ++ " ^ " ++ non_hof_argDecls !! 1
          "not" -> "!" ++ non_hof_argDecls !! 0
          "eq" -> non_hof_argDecls !! 0 ++ " == " ++ non_hof_argDecls !! 1
          "neq" -> non_hof_argDecls !! 0 ++ " != " ++ non_hof_argDecls !! 1
          "lt" -> non_hof_argDecls !! 0 ++ " < " ++ non_hof_argDecls !! 1
          "leq" -> non_hof_argDecls !! 0 ++ " <= " ++ non_hof_argDecls !! 1
          "gt" -> non_hof_argDecls !! 0 ++ " > " ++ non_hof_argDecls !! 1
          "geq" -> non_hof_argDecls !! 0 ++ " >= " ++ non_hof_argDecls !! 1
          _ -> "unsupported primitive builtin"
    let
      sieve_non_hof_call =
        writeUnfinishedLine ctx $
            (if isUnitType resTypeF then "value_to_unit(&" else "") ++
            "call_sieve(ctx, stack, (" ++ outputModuli ++ ", vec![" ++ intercalate ", " inputModuli ++ "]), vec![" ++
            intercalate ", " hof_typeArgDecls ++ "], vec![" ++ intercalate ", " hof_argDecls ++ "], " ++ show fname ++ ".to_string(), " ++ fname ++ "_hof)" ++
            (if isUnitType resTypeF then ")" else "")
    let hof_call f = writeUnfinishedLine ctx $ "call_hof_next(ctx, &mut stack.scope(), " ++ f
                         ++ ", vec![" ++ intercalate ", " hof_typeArgDecls ++ "]"
                         ++ ", vec![" ++ intercalate ", " hof_argDecls ++ "]"
                         ++ ", " ++ outputModuli
                         ++ ", vec![" ++ intercalate ", " inputModuli ++ "])"
    let hof_call_initial f n1 n2 = writeUnfinishedLine ctx $ "call_hof_initial(ctx, "
                                       ++ f ++ "_hof, "
                                       ++ show f ++ ", "++ show n1 ++ ", " ++ show n2
                                       ++ ", vec![" ++ intercalate ", " hof_typeArgDecls ++ "]"
                                       ++ ", vec![" ++ intercalate ", " hof_argDecls ++ "]"
                                       ++ ", vec![" ++ intercalate ", " (if isSieve then inputModuli else []) ++ "]"
                                       ++ ", " ++ (if isSieve then "true" else "false") ++ ")"
    let is_hof_call =
            case Map.lookup f _globalFunMap of
                Nothing
                    | isBuiltinVar f -> False
                    | otherwise -> True
                Just (numTypeArgs, numValueArgs)
                    | length typeArgDecls == numTypeArgs && length argDecls == numValueArgs -> False
                    | otherwise -> True
    let convert_result_to_primitive = isTypePrimitive resType && (is_hof_call || (not is_primitive_builtin && not (isTypePrimitive resTypeF)))
    when convert_result_to_primitive $ writeUnfinishedLine ctx $ valueToPrimitive0 resType ++ "("
    if is_primitive_builtin
      then primitive_builtin_call
      else
        (if isTypePrimitive resTypeF && not is_hof_call then (if isUnitType resTypeF then callWithLocUnit ctx (Right f) loc else id) else callWithLoc ctx (Right f) loc) $
            case Map.lookup f _globalFunMap of
                Nothing
                    | isBuiltinVar f -> non_hof_call
                    | otherwise -> hof_call fname
                Just (numTypeArgs, numValueArgs)
                    | length typeArgDecls == numTypeArgs && length argDecls == numValueArgs -> if isSieve then sieve_non_hof_call else non_hof_call
                    | otherwise -> hof_call_initial fname numTypeArgs numValueArgs
    when convert_result_to_primitive $ writeUnfinishedLine ctx $ ")"
  CeMatch x cases defaultCase xs -> do
    let fs = defaultCase : map snd cases
    let ints = map fst cases
    let xModulus = uintNToRefNatTypeRust (idToType x)
    let inputModuli = flip map xs $ \ x -> sizedTypeToRefNatTypesOrPrePublicRust (idToType x)
    let resType = idToType recRetVar
    let outputModuli = sizedTypeToRefNatTypesRust resType
    let argDecls = map varToString xs
    let hof_argDecls = map (++ ".clone()") argDecls
    let fnames = map varToString fs
    let fnames_str = "vec![" ++ intercalate ", " (map ((++ ".to_string()") . show) fnames) ++ "]"
    let fnames_hof = "vec![" ++ intercalate ", " fnames ++ "]"
    let ints_str = "vec![" ++ intercalate ", " (map ((\ s -> "int_lit(" ++ s ++ ")") . show . show) ints) ++ "]"
    writeUnfinishedLine ctx $
        "&match_sieve(ctx, stack, " ++ varToString x ++ ", " ++ xModulus ++ ", " ++ ints_str ++ ", (" ++ outputModuli ++ ", vec![" ++
        intercalate ", " inputModuli ++ "]), vec![" ++ intercalate ", " hof_argDecls ++ "], " ++ fnames_str ++ ", " ++ fnames_hof ++ ")"
  CeTrace _loc str expr ->
    do
      writeUnfinishedLine ctx $ (if isTypePrimitive (idToType recRetVar) then "" else "&") ++ "with_trace(ctx," ++ show str ++ ", ||"
      writeLine ctx "{"
      translateLet ctx expr
      writeUnfinishedLine ctx "})"
  CeDbgAssert x l mcl -> callWithLocUnit ctx (Left "dbg_assert") l $ do
    let t = idToType x
    let d = typeToDomainTypeRust t
    let natTy = uintNToRefNatTypeRust t
    if isTypePrimitive t
      then writeUnfinishedLine ctx $ "dbg_assert_bool(ctx, " ++ d ++ ", " ++ idToString x ++ ", " ++ show (render (pretty l)) ++ ", "
      else writeUnfinishedLine ctx $ "dbg_assert(ctx, " ++ d ++ ", " ++ natTy ++ ", " ++ idToString x ++ ", " ++ show (render (pretty l)) ++ ", "
    translateDebugMcl ctx mcl
    writeUnfinishedLine ctx $ ")"
  CeDbgAssertEq x y l mcl -> callWithLocUnit ctx (Left "dbg_assert_eq") l $ do
    let t = idToType x
    let d = typeToDomainTypeRust t
    let natTy = uintNToRefNatTypeRust t
    if isTypePrimitive t
      then writeUnfinishedLine ctx $ "dbg_assert_eq_" ++ primitiveToRustType t ++ "(ctx, " ++ d ++ ", " ++ idToString x ++ ", " ++ idToString y ++ ", " ++ show (render (pretty l)) ++ ", "
      else writeUnfinishedLine ctx $ "dbg_assert_eq(ctx, " ++ d ++ ", " ++ natTy ++ ", " ++ idToString x ++ ", " ++ idToString y ++ ", " ++ show (render (pretty l)) ++ ", "
    translateDebugMcl ctx mcl
    writeUnfinishedLine ctx $ ")"
  _ -> error $ "translateExpr: Unsupported Core expression: " ++ showCoreExpr e
  where ?ctx = ctx

-- TODO: If debugging is disabled we should not emit locations here.
callWithLoc :: Context -> Either String Var -> Location -> IO () -> IO ()
callWithLoc ctx mf loc cont = do
    let callStr = case mf of
            Left name -> pretty name <+> "at" <+> pretty loc
            Right f -> pretty (nameOccName (varName f)) <+> "at" <+> pretty loc
    writeUnfinishedLine ctx $ "&with_loc(ctx," ++ show (render callStr) ++ ", || {"
    cont
    writeUnfinishedLine ctx "})"

-- TODO: If debugging is disabled we should not emit locations here.
callWithLocUnit :: Context -> Either String Var -> Location -> IO () -> IO ()
callWithLocUnit ctx mf loc cont = do
    let callStr = case mf of
            Left name -> pretty name <+> "at" <+> pretty loc
            Right f -> pretty (nameOccName (varName f)) <+> "at" <+> pretty loc
    writeUnfinishedLine ctx $ "with_loc_unit(ctx," ++ show (render callStr) ++ ", || {"
    cont
    writeUnfinishedLine ctx "})"

translateBind :: Context -> CoreBind -> IO ()
translateBind ctx@Ctx{..} (CoreBind recursive (CorePat [x]) e) = do
  let isRef = case e of CeRef{} -> True; _ -> False
  let primitiveMutable = idIsMutable x && isTypePrimitive (idToType x)
  unless isRef $ writeUnfinishedLine ctx $ "let " ++ (if primitiveMutable then "mut " else "") ++ varToString x ++ " = "
  let mutable = idIsMutable x && not primitiveMutable
  let immutToMut = mutable && not isRef -- refs are already mutable
  when immutToMut $ writeUnfinishedLine ctx $ "&mut immutable_to_mutable(ctx, "
  when recursive $ modifyIORef _recursiveVars $ Set.insert x
  translateExpr ctx x e
  when recursive $ modifyIORef _recursiveVars $ Set.delete x
  when immutToMut $ writeUnfinishedLine ctx $ ")"
  unless isRef $ writeLine ctx ";"
translateBind _ (CoreBind _ (CorePat xs) _) = error $ "translateBind: multiple (or zero) bound variables not supported: " ++ show (map varToString xs)

translateLet :: Context -> CoreLet -> IO ()
translateLet ctx (CoreLet binds [retVar]) = do
  increaseIndent ctx
  forM_ binds (translateBind ctx)
  writeLine ctx $ varToString retVar ++ (if isTypePrimitive (idToType retVar) then "" else ".clone()")
  decreaseIndent ctx
translateLet _ (CoreLet _ retVars) = error $ "translateLet: multiple (or zero) return variables not supported: " ++ show (map varToString retVars)

translateLetWithPrefixAndSuffix :: Context -> CoreLet -> IO () -> IO () -> IO ()
translateLetWithPrefixAndSuffix ctx (CoreLet binds [retVar]) prefix suffix = do
  increaseIndent ctx
  prefix
  forM_ binds (translateBind ctx)
  suffix
  writeLine ctx $ varToString retVar ++ (if isTypePrimitive (idToType retVar) then "" else ".clone()")
  decreaseIndent ctx
translateLetWithPrefixAndSuffix _ (CoreLet _ retVars) _ _ = error $ "translateLet: multiple (or zero) return variables not supported: " ++ show (map varToString retVars)

translateLetWithTypeChange :: Context -> Type Var -> CoreLet -> IO ()
translateLetWithTypeChange ctx resType (CoreLet binds [retVar]) = do
  increaseIndent ctx
  forM_ binds (translateBind ctx)
  writeLine ctx $
    case (isTypePrimitive (idToType retVar), isTypePrimitive resType) of
      (True, True) -> varToString retVar
      (False, False) -> varToString retVar ++ ".clone()"
      (True, False) -> let ?ctx = ctx in varToClonedValue retVar
      (False, True) -> error "translateLetWithTypeChange"
  decreaseIndent ctx
translateLetWithTypeChange _ _ (CoreLet _ retVars) = error $ "translateLet: multiple (or zero) return variables not supported: " ++ show (map varToString retVars)

translateWireExpr :: Context -> Var -> CoreLet -> IO ()
translateWireExpr ctx xlen (CoreLet binds [retVar]) = do
  increaseIndent ctx
  forM_ binds (translateBind ctx)
  let ?ctx = ctx
  let t = typeToValueTypeRust (idToType retVar)
  let xlen' = if isTypePrimitive (idToType xlen) then "&ctx.scalar" else varToString xlen
  writeLine ctx $ "wire(ctx, " ++ t ++ ", " ++ xlen' ++ ", " ++ varToBorrowedValue retVar ++ ")"
  decreaseIndent ctx
translateWireExpr _ _ (CoreLet _ retVars) = error $ "translateWireExpr: multiple (or zero) return variables not supported: " ++ show (map varToString retVars)

header :: String
header = "\
    \/*\n\
    \ * Copyright 2024 Cybernetica AS\n\
    \ * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:\n\
    \ * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.\n\
    \ * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.\n\
    \ * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.\n\
    \ * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.\n\
    \ */\n\n\
    \/*\n\
    \ * WARNING! WARNING! WARNING!\n\
    \ * This file is automatically generated by the ZKSC compiler.\n\
    \ * WARNING! WARNING! WARNING!\n\
    \ */\n\n\
    \#![allow(unused_macros, unconditional_recursion, unused_variables, non_snake_case, dead_code, unreachable_code, non_upper_case_globals, non_camel_case_types, unused_imports)]\n\
    \use std::rc::Rc;\n\
    \use crate::sieve::*;\n\
    \use crate::context::*;\n\
    \use crate::zksc_types::*;\n\
    \use crate::builtins::*;\n\
    \use crate::integer::*;\n\
    \use crate::value::*;\n\
    \use crate::value_conversions::*;\n\
    \use num_integer::Integer;\n\
    \use crate::consts::*;\n\
    \use crate::stack::*;\n\n\
    \use num_bigint::BigInt;\n\
    \use num_bigint::Sign;\n\
    \use once_cell::sync::OnceCell;\n\
    \use num_traits::Zero;\n\
    \use num_traits::One;\n\
    \use crate::zksc_integer::*;"

entryPointParameters :: String
entryPointParameters = "\
    \input_public: Option<&str>, \
    \input_instance: Option<&str>, \
    \input_witness: Option<&str>, \
    \circuit_content_loader: ResourceLoader<str>, "

bytesPerLimb :: Int
bytesPerLimb = 8

-- Probably never, but never know...
bitsPerByte :: Int
bitsPerByte = 8

maxLimb :: Natural
maxLimb = limbModulus - 1

limbModulus :: Natural
limbModulus = 2 ^ (bytesPerLimb * bitsPerByte)

widthInBits :: (Integral a, Num b) => a -> b
widthInBits 0 = 0
widthInBits m = 1 + widthInBits (m `div` 2)

getLimbCount :: Natural -> Int
getLimbCount n | n <= limbModulus = 1
               | otherwise = 1 + getLimbCount ((n + maxLimb) `div` limbModulus)

natToBeHex :: Natural -> Int -> String
natToBeHex n limbs = printf fmt n
    where fmt = "\"%0" ++ show (2 * bytesPerLimb * limbs) ++ "x\""

fieldName :: Natural -> String
fieldName n | n `elem` primitiveUints = primitiveModulusToRustType n
            | otherwise = "PrimeField" ++ show n

definePrimeFieldType :: Context -> Natural -> IO ()
definePrimeFieldType ctx n
  | n == 0 = return () -- inf, already sorted
  | n `elem` primitiveUints = return () -- u64, etc., already sorted
  | n <= maxLimb = do
    let args = name ++ ",u64"
    writeLine ctx $ "small_modulus_struct!{" ++ args ++ ","++ show n ++ "}"
    defineFunc ctx $ do
        writeLine ctx $ "small_modulus_nattype!(" ++ args ++ "," ++ show n ++ ")"
  | otherwise = do
    let args = name ++ ", " ++ natToBeHex n limbCount
    writeLine ctx $ "fixed_modulus_struct!{" ++ args ++ "}"
    defineFunc ctx $ do
        writeLine ctx $ "fixed_modulus_nattype!(" ++ name ++ ")"
  where
    name = fieldName n
    limbCount = getLimbCount n
    defineFunc ctx act = do
        writeLine ctx $ "fn nattype_" ++ show n ++ "() -> NatType {"
        withIncreasedIndent ctx act
        writeLine ctx "}"

registerPrimeFieldStructs :: Context -> [Natural] -> IO ()
registerPrimeFieldStructs ctx nats = do
  writeLine ctx "#[macro_export]"
  writeLine ctx "macro_rules! for_each_zksc_type {"
  withIncreasedIndent ctx $ do
    writeLine ctx "($continuation:ident) => {"
    withIncreasedIndent ctx $ do
        writeLine ctx "$continuation! {"
        withIncreasedIndent ctx $ do
            writeLine ctx "(BigInt,0),"
            forM_ (zip nats [1 ..]) $ \(n, i) -> do
                writeLine ctx $ "(" ++ fieldName n ++ "," ++ show i ++ "),"
        writeLine ctx "}"
    writeLine ctx "};"
  writeLine ctx "}"

isPluginIter :: T.Text -> Bool
isPluginIter t =
  case T.unpack t of
    "iter" -> True
    'i' : 't' : 'e' : 'r' : '_' : 'v' : _ -> True
    _ -> False

choosePlugin :: Bool -> [Versioned T.Text] -> [(T.Text, String)]
choosePlugin iterUnconditionallyNeeded = \case
  [] -> []
  ps ->
    let
      p = last ps
      name = T.unpack (_versionedName p)
      vers = map _versionedVer ps
    in
      case name of
        "iter" | [0] `elem` vers -> [("iter_v0", name)]
               | iterUnconditionallyNeeded -> error "Plugin iter needed but version 0 not supported by CCC"
               | otherwise -> [] -- iter only needed inside if (Vectorization) { ... } blocks, which can be skipped
        _ -> [((T.pack . render. pretty) p, name)] -- chooses the last version

writeHeader :: Context -> TestData -> Bool -> Bool -> [Natural] -> IO ()
writeHeader ctx testData iterUnconditionallyNeeded areExternsUsed mainTypeArgs = do
  writeLine ctx header
  when areExternsUsed $ writeLine ctx "use crate::externs::*;"
  writeLine ctx "use crate::externs_stdlib::*;"
  let nats = [n | Finite n <- map fst $ sortOn (fst . snd) $ Map.toList (_natLiteralIndices ctx)]
  mapM_ (definePrimeFieldType ctx) nats
  registerPrimeFieldStructs ctx nats
  writeLine ctx $ "pub fn run(" ++ entryPointParameters ++ ") -> Result<()> {"
  withIncreasedIndent ctx $ do
    writeLine ctx "// Build cache for integer literals"
    writeLine ctx "let integer_literals = vec!["
    withIncreasedIndent ctx $ do
      forM_ (sortOn snd (Map.toList (_literalIndices ctx))) $ \(literal, (_, count)) -> do
        writeLine ctx $ "int_lit(" ++ show (show literal) ++ "), // count: " ++ show count
    writeLine ctx "];"
    writeLine ctx "// Build cache for string literals"
    writeLine ctx "let string_literals = vec!["
    withIncreasedIndent ctx $ do
      forM_ (sortOn snd (Map.toList (_strLiteralIndices ctx))) $ \(literal, (_, count)) -> do
        writeLine ctx $ "rep::Str::new(String::from(" ++ stringLiteralToRust literal ++ ")), // count: " ++ show count
    writeLine ctx "];"
    writeLine ctx "// Build list of all possible Nat types"
    writeLine ctx "let nat_type_literals = vec!["
    withIncreasedIndent ctx $ do
      forM_ (zip [0 ..] (sortOn snd (Map.toList (_natLiteralIndices ctx)))) $ \(tag, (literal, (_, count))) -> do
         writeLine ctx $ case literal of
            Infinite -> "infinite_nattype(), // count: " ++ show count
            Finite n
              | n `elem` primitiveUints -> "nattype_" ++ show n ++ "(" ++ show tag ++ "), // count: " ++ show count
              | otherwise -> "nattype_" ++ show n ++ "(), // count: " ++ show count
    writeLine ctx "];"
    writeLine ctx "// Build list of supported fields"
    writeLine ctx "let supported_fields = vec!["
    withIncreasedIndent ctx $ do
      forM_ (_supportedFields testData) $ \ n ->
        writeLine ctx $ "BigInt::parse_bytes(b\"" ++ show n ++ "\", 10).unwrap(),"
    writeLine ctx "];"
    writeLine ctx "// Build list of supported challenges"
    writeLine ctx "let supported_challenges = vec!["
    withIncreasedIndent ctx $ do
      forM_ (_supportedChallenges testData) $ \ n ->
        writeLine ctx $ "BigInt::parse_bytes(b\"" ++ show n ++ "\", 10).unwrap(),"
    writeLine ctx "];"
    writeLine ctx "// Build list of supported conversions"
    writeLine ctx "let supported_conversions = vec!["
    withIncreasedIndent ctx $ do
      forM_ (_supportedConverts testData) $ \ (n1, n2) ->
        writeLine ctx $
          "(BigInt::parse_bytes(b\"" ++ show n1 ++ "\", 10).unwrap()," ++
          "BigInt::parse_bytes(b\"" ++ show n2 ++ "\", 10).unwrap()),"
    writeLine ctx "];"
    let (plugins, pluginsNonversioned) = unzip $ concatMap (choosePlugin iterUnconditionallyNeeded) $ _supportedPlugins testData
    let is_iter_available = any isPluginIter plugins
    writeLine ctx $ "let is_iter_available = " ++ (if is_iter_available then "true" else "false") ++ ";"
    writeLine ctx "let supported_plugins = vec!["
    withIncreasedIndent ctx $ do
      forM_ plugins $ \ s ->
        writeLine ctx $ show s ++ ","
    writeLine ctx "];"
    writeLine ctx "let supported_plugins_nonversioned = vec!["
    withIncreasedIndent ctx $ do
      forM_ pluginsNonversioned $ \ s ->
        writeLine ctx $ show s ++ ","
    writeLine ctx "];"
    let
      natLit n =
        case Map.lookup (Finite (fromInteger n)) (_natLiteralIndices ctx) of
          Just idx -> "&nat_type_literals[" ++ show (fst idx) ++ "]"
          Nothing -> "/* " ++ show n ++ " */"
    writeLine ctx "let supported_conversions_nattype = vec!["
    withIncreasedIndent ctx $ do
      forM_ (_supportedConverts testData) $ \ (n1, n2) ->
        writeLine ctx $ "(" ++ natLit n1 ++ ", " ++ natLit n2 ++ "),"
    writeLine ctx "];"
    writeLine ctx $ "sieve_backend().write_headers(&nat_type_literals[0 .. " ++ show (1 + _numPostModuli ctx) ++ "].to_vec(), supported_conversions_nattype, supported_plugins);"
    writeLine ctx "let ctx = Context::new(input_public, input_instance, input_witness, circuit_content_loader, integer_literals, string_literals, nat_type_literals.clone(), supported_fields, supported_challenges, supported_conversions, is_iter_available, supported_plugins_nonversioned)?;"
    writeLine ctx "let ctx = &Rc::new(ctx);"
    writeLine ctx "let stack_memory = StackMemory::new(10 * 1024 * 1024);" -- 10 megabytes
    writeLine ctx "let mut stack = stack_memory.try_lock().unwrap();"
    writeLine ctx $ "main0(ctx, &mut stack" ++ concatMap ((", " ++) . natLit . toInteger) mainTypeArgs ++ ");"
    writeLine ctx "ctx.finalize()?;"
    writeLine ctx "Ok(())"
  writeLine ctx "}"

withMaybeFile :: Maybe FilePath -> (Handle -> IO a) -> IO a
withMaybeFile Nothing cont = cont stdout
withMaybeFile (Just filePath) cont = withFile filePath WriteMode cont

coreToRust :: StructsEnv -> Maybe FilePath -> TestData -> CoreProgram -> IO ()
coreToRust senv mOutputPath testData prog@CoreProgram{..} =
  let
    funcParamPassingStyle (SimpleFuncParam pps _) = pps
    functionInfo CoreTopFunction{..} =
      let
        fname = funIdToString _coreFunName
        argIds = map funcParamName _coreFunArgs
        isSieve = _coreFunIsSieve == IsSieveFn
        isLambda = _coreFunIsLambda == IsLambda
        isExtern = False
      in
        (fname,
         (_coreFunName,
          idType _coreFunName,
          (argIds, map funcParamPassingStyle _coreFunArgs),
          removeCopiesFromCoreLet _coreFunBody,
          isSieve, isLambda, isExtern))
    externInfo CoreTopExtern{..} =
      let
        fname = idToBaseString _coreExtName
        argIds = map funcParamName _coreExtArgs
        isSieve = False
        isLambda = False
        isExtern = True
      in
        (fname,
         (_coreExtName,
          idType _coreExtName,
          (argIds, map funcParamPassingStyle _coreExtArgs),
          undefined,
          isSieve, isLambda, isExtern))
    globalFunList = map functionInfo (flattenSCCs _coreFunctions) ++ map externInfo _coreExterns
    externSet = Set.fromList $ map _coreExtName _coreExterns
    areExternsUsed = not $ Set.null externSet
    sieveFunList = filter (\ (_, (_, _, _, _, isSieve, _, _)) -> isSieve) globalFunList
    sieveFunIds = map (\ (_, (fvar, _, _, _, _, _, _)) -> fvar) sieveFunList
    -- sort the literals by the frequency of use to improve cache locality
    buildFreqList xs = sortOn (negate.snd) $ Map.toList $ Map.fromListWith (+) [(x, 1) | x <- xs]
    buildLookupMap xs = Map.fromList $ [(n, (index, count)) | ((n, count), index) <- zip xs [0 ..]]
    literals = toListOf litsInCoreProgram prog
    intLiterals = buildFreqList [n | ConstInt n <- literals]
    literalIndices = buildLookupMap intLiterals
    -- main functions are sorted topologically and in order of imports
    -- thus the main function will be the last' one with name "main"
    mains = [mainId | (fname, (mainId, _, _, _, _, _, _)) <- globalFunList, fname == T.unpack mainFName]
    mainId = last' mains
    (iterUnconditionallyNeeded, mainTypeVars) =
      if null mains
        then (False, [])
        else
          case idType mainId of
            TForAll tvars preds _ -> (
              flip any preds $ \ case
                 PredVectorization _ -> True
                 _ -> False,
              tvars)
    mainTypeArgs = map (fromInteger . flip findUM (mapUM unLocated (_mainTypeParamsEval testData))) mainTypeVars
    natsUnordered = buildFreqList [Finite n | n <- toListOf (definedVarsInCoreProgram.typesInVar.natLiteralsInType) prog ++ mainTypeArgs, n `notElem` primitiveUints]
    ns = sortOn fst natsUnordered
    (ns_post, ns_only_pre) = flip partition ns $ \ (en, _) ->
      case en of
        Infinite -> False
        Finite n -> (n `notElem` primitiveUints) && (toInteger n `elem` _supportedFields testData)
    nats = (Infinite, 0) : ns_post ++ ns_only_pre ++ [(Finite n, 0) | n <- primitiveUints]
    natLiteralIndices = buildLookupMap nats
    strLiterals = buildFreqList [s | ConstString s <- literals]
    strLiteralIndices = buildLookupMap strLiterals
  in withMaybeFile mOutputPath $ \handle -> do
    indent <- newIORef ""
    lineFinished <- newIORef True
    recursiveVars <- newIORef Set.empty
    refArgMap <- newIORef Map.empty
    structsWithFinalizer <- newIORef Set.empty
    let globalFunMap = Map.fromList $ flip map globalFunList $ \ (_, (fvar, TForAll ts _ _, (vs, _), _, _, _, _)) -> (fvar, (length $ filter (isKindPassed . tyVarKind) ts, length vs))
    let ctx = Ctx { _indent = indent, _lineFinished = lineFinished, _recursiveVars = recursiveVars,
                    _literalIndices = literalIndices,
                    _natLiteralIndices = natLiteralIndices,
                    _strLiteralIndices = strLiteralIndices,
                    _numPostModuli = length ns_post,
                    _refArgMap = refArgMap,
                    _globalFunMap = globalFunMap,
                    _externSet = externSet,
                    _structsEnv = senv,
                    _structsWithFinalizer = structsWithFinalizer,
                    _sieveFunSet = Set.fromList sieveFunIds,
                    _handle = handle,
                    _isInsideSieveFn = False }
    -- Limit warning supression to only generated code.
    -- We should follow rust code style recommendations elsewhere.
    writeHeader ctx testData iterUnconditionallyNeeded areExternsUsed mainTypeArgs
    let
      processFunction isMethod (fname0, (id, TForAll ts _ ftype, (argIds, argPassingStyles), funBody, isSieve, isLambda, isExtern)) = do
        let isMain = not (null mains) && id == mainId
        let fname = if isMain then "main0" else fname0 -- there will be another main function written in Rust, which will call main0
        let
          kindToRust = \case
            KindNat -> "&NatType"
            KindStage -> "StageType"
            KindDomain -> "DomainType"
            KindStar -> "QualifiedType"
            _ -> ""
        let
          typeArgToRust x =
            case kindToRust (tyVarKind x) of
              "" -> Nothing
              s -> Just (varToString x ++ ": " ++ s)
          typeArgToRustWithoutType x =
            case kindToRust (tyVarKind x) of
              "" -> Nothing
              '&' : _ -> Just ('&' : varToString x)
              _ -> Just (varToString x)
          -- we need to clone the references so that the finalizer closure can take the ownership
          cloneTypeArgForClosure x =
            case kindToRust (tyVarKind x) of
              '&' : _ -> let x' = varToString x in writeLine ctx $ "let " ++ x' ++ " = " ++ x' ++ ".clone();"
              _ -> return ()
        let typeArgDecls = mapMaybe typeArgToRust ts
        let typeArgDeclsWithoutType = mapMaybe typeArgToRustWithoutType ts
        let
          idIsPrimitiveMutable x = idIsMutable x && isTypePrimitive (idToType x)
          argTypeDecl x pps =
            let t = idToType x
            in
              if isTypePrimitive t
                then
                  case pps of
                    PassByValue -> primitiveToRustType t
                    PassByRef -> "&mut " ++ primitiveToRustType t
                else
                  case pps of
                    PassByValue | isExtern -> zkscToExternRustTypeArg t
                                | otherwise -> "&Value"
                    PassByRef -> "&mut Value"
        let argDecls = zipWith (\ x pps -> varToString x ++ (if idIsPrimitiveMutable x then "_mut" else "") ++ ": " ++ argTypeDecl x pps) argIds argPassingStyles
        let primitiveMutableVarNames = map varToString $ filter idIsPrimitiveMutable argIds
        let numArgs = length argIds
        let numArgs' = if numArgs == 0 && isUnitArgFunc ftype then 1 else numArgs
        let (argTypes, _) = splitFuncTypeN ftype numArgs
        let (_, resType) = splitFuncTypeN ftype numArgs'
        let resTypeDecl = if isTypePrimitive resType then primitiveToRustType resType else (if isExtern then zkscToExternRustType resType else "Value")
        let isAnyArgRef = any (\case PassByRef -> True; _ -> False) argPassingStyles
        when (isSieve && not isLambda) $ do
          let ?ctx = ctx in do
            let outputModuli = sizedTypeToRefNatTypesRust resType
            let inputModuli = map sizedTypeToRefNatTypesRust argTypes
            writeLine ctx ""
            writeLine ctx $ "fn " ++ fname ++ "_moduli<'a>(ctx: &'a ContextRef" ++ concatMap ((", " ++) . addLifetimes) typeArgDecls ++ ") -> (SoA<&'a NatType>, Vec<SoA<&'a NatType>>) {"
            withIncreasedIndent ctx $
              writeLine ctx $ "(" ++ outputModuli ++ ", vec![" ++ intercalate ", " inputModuli ++ "])"
            writeLine ctx "}"
        writeLine ctx ""
        writeLine ctx $ "fn " ++ fname ++ "_hof(ctx: &ContextRef, stack: &mut Stack, ts: &Vec<TypeEnum>, vs: &Vec<Value>) -> Value {"
        withIncreasedIndent ctx $
          if isAnyArgRef then
            writeLine ctx $ "panic!(\"Function " ++ fname ++ " cannot be used as a higher-order function because it has a ref argument\");"
          else let ?ctx = ctx in do
            let get_te t = case tyVarKind t of
                             KindNat -> Just "nat"
                             KindStage -> Just "stage"
                             KindDomain -> Just "domain"
                             KindStar -> Just "qualified"
                             _ -> Nothing
            let typeArgs = flip map (zip [0..] (mapMaybe get_te ts)) $ \ (i,te) -> "get_te" ++ te ++ "(&ts[" ++ show i ++ "])"
            let typeStrs = map varToString $ filter (isJust . get_te) ts
            let domainStr = typeToDomainTypeRust resType
            let domainArgs = filter ((== domainStr) . snd) $ zip typeArgs typeStrs
            let domainArg = if null domainArgs then domainStr else fst $ head domainArgs
            let valueArgs = flip map (zip [0..] argTypes) $ \ (i,t) ->
                                let x = "&vs[" ++ show i ++ "]"
                                in (if isExtern then valueToExternIfNecessary else valueToPrimitiveIfNecessary) t x
            let fcall = fname ++ "(ctx, &mut stack.scope()" ++ concatMap (", " ++) (typeArgs ++ valueArgs) ++ ")"
            writeLine ctx $ if isTypePrimitive resType
                              then primitiveToValueD domainArg resType fcall
                              else
                                if isExtern && isNonPrimitiveExtern resType
                                  then fcall ++ ".into()"
                                  else fcall
        writeLine ctx "}"
        unless isExtern $ do
          writeLine ctx ""
          writeLine ctx $ "fn " ++ fname ++ "(ctx: &ContextRef, stack: &mut Stack" ++ concatMap (", " ++) (typeArgDecls ++ argDecls) ++ ") -> " ++ resTypeDecl ++ " {"
          let
            action1 =
              forM_ primitiveMutableVarNames $ \ x ->
                writeLine ctx $ "let mut " ++ x ++ " = *" ++ x ++ "_mut;"
          let
            action2 =
              forM_ primitiveMutableVarNames $ \ x ->
                writeLine ctx $ "*" ++ x ++ "_mut = " ++ x ++ ";"
          translateLetWithPrefixAndSuffix (ctx { _isInsideSieveFn = isSieve }) funBody action1 action2
          writeLine ctx "}"
        when isExtern $ do
          writeLine ctx ""
          writeLine ctx $ "// fn " ++ fname ++ "(ctx: &ContextRef, stack: &mut Stack" ++ concatMap (", " ++) (typeArgDecls ++ argDecls) ++ ") -> " ++ resTypeDecl ++ ";"
        if isMethod && idToBaseString id == "finalize" then do
          writeLine ctx ""
          writeLine ctx $ "pub fn get_finalizer(ctx: &ContextRef" ++ concatMap (", " ++) typeArgDecls ++ ") -> FinalizerRef {"
          withIncreasedIndent ctx $ do
            mapM_ cloneTypeArgForClosure ts
            writeLine ctx $ "Some(Rc::new(Finalizer::new(ctx, Box::new(move |ctx: &ContextRef, stack: &mut Stack, x: &Value| { " ++ fname ++ "(ctx, stack" ++ concatMap (", " ++) typeArgDeclsWithoutType ++ ", x); }))))"
          writeLine ctx "}"
          return True
        else
          return False
    forM_ _coreStructImpls $ \ CoreStructImpl{..} -> do
      writeLine ctx ""
      writeLine ctx ("mod struct_" ++ render (pretty _coreImplType) ++ " {")
      let funList = map functionInfo _coreImplMethods
      withIncreasedIndent ctx $ do
        writeLine ctx "use super::*;"
        isFinalizes <- forM funList (processFunction True)
        let s = case _coreImplType of TVar x _ _ -> x; _ -> error "Struct name in an impl must be a Var"
        when (or isFinalizes) $
          modifyIORef structsWithFinalizer $ Set.insert s
      writeLine ctx "}"
    forM_ globalFunList (processFunction False)
