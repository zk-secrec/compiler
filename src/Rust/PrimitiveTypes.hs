{-# LANGUAGE LambdaCase #-}

module Rust.PrimitiveTypes where

import Basic.Var
import Typing.Type

import GHC.Natural (Natural)
import Data.List

primitiveUints :: [Natural]
primitiveUints = [2^8, 2^16, 2^32, 2^64, 2^128]

primitiveModulusToRustType :: Natural -> String
primitiveModulusToRustType m
  | m == 2^8 = "u8"
  | m == 2^16 = "u16"
  | m == 2^32 = "u32"
  | m == 2^64 = "u64"
  | m == 2^128 = "u128"
  | otherwise = error "Not a primitive modulus"

-- uint[2^32/2^64] $pre @D or bool[N] $pre @D or () $pre @D
isTypePrimitive :: Type TyVar -> Bool
isTypePrimitive = \case
  TQualify (TUInt (TNat (Finite m))) (TStage TVPre) _ -> m `elem` primitiveUints
  TQualify (TBin _) (TStage TVPre) _ -> True
  TQualify TUnit (TStage TVPre) _ -> True
  _ -> False

-- the name of the Rust type corresponding to the given primitive type
primitiveToRustType :: Type TyVar -> String
primitiveToRustType = \case
  TQualify (TUInt (TNat (Finite m))) (TStage TVPre) _ | m `elem` primitiveUints -> primitiveModulusToRustType m
  TQualify (TBin _) (TStage TVPre) _ -> "bool"
  TQualify TUnit (TStage TVPre) _ -> "unit"
  _ -> error "Not a primitive type"

-- primitive values cannot contain Unknowns, they are replaced by some default values
unknownPrimitive :: Type TyVar -> String
unknownPrimitive = \case
  TQualify (TUInt (TNat (Finite m))) (TStage TVPre) _ | m `elem` primitiveUints -> "0" ++ primitiveModulusToRustType m
  TQualify (TBin _) (TStage TVPre) _ -> "false"
  TQualify TUnit (TStage TVPre) _ -> "()"
  _ -> error "Not a primitive type"

-- the name of the Rust function that converts the given primitive type to Value
primitiveToValue0 :: Type TyVar -> String
primitiveToValue0 t = primitiveToRustType t ++ "_to_value"

-- the name of the Rust function that converts the given primitive type to Value
valueToPrimitive0 :: Type TyVar -> String
valueToPrimitive0 t = "value_to_" ++ primitiveToRustType t

-- the name of the extern Rust type (used in extern Rust functions called from ZKSC) corresponding to the given ZKSC type
zkscToExternRustType0 :: String -> Type TyVar -> String
zkscToExternRustType0 prefix = \case
  t | isTypePrimitive t -> primitiveToRustType t
  TQualify (TUInt (TNat Infinite)) (TStage TVPre) _ -> prefix ++ "BigInt"
  TQualify TString (TStage TVPre) _ -> prefix ++ "String"
  TQualify (TList (TQualify TUnit (TStage TVPre) _)) _ _ -> prefix ++ "Value"
  TQualify (TList t) _ _ | isTypePrimitive t -> prefix ++ "Vec<" ++ primitiveToRustType t ++ ">"
                         | otherwise -> prefix ++ "Vec<Value>"
  TQualify (TArr (TQualify TUnit (TStage TVPre) _)) _ _ -> prefix ++ "Value"
  TQualify (TArr t) _ _ | isTypePrimitive t -> prefix ++ "Vec<" ++ primitiveToRustType t ++ ">"
                        | otherwise -> prefix ++ "Vec<Value>"
  TQualify (TTuple ts) _ _ | length ts <= 5 -> "(" ++ intercalate ", " (map (zkscToExternRustType0 prefix) ts) ++ ")"
                           | otherwise -> prefix ++ "Box<[Value]>"
  _ -> prefix ++ "Value"

zkscToExternRustType :: Type TyVar -> String
zkscToExternRustType = zkscToExternRustType0 ""

zkscToExternRustTypeArg :: Type TyVar -> String
zkscToExternRustTypeArg = zkscToExternRustType0 "&"

isNonPrimitiveExtern :: Type TyVar -> Bool
--isNonPrimitiveExtern t = not (isTypePrimitive t) && zkscToExternRustType t /= "Value"
isNonPrimitiveExtern t = not (isTypePrimitive t) -- for structs to work, use .into() on all non-primitives
