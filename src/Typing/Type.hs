{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE ViewPatterns #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Typing.Type (
  DomainType,
  GetInputFn(..),
  Kind(..),
  Level,
  Mutability(..),
  NatType,
  QualifiedType,
  SemiRing(..),
  StageType,
  TVDomain(..),
  TVStage(..),
  TVKBool(..),
  Type(..),
  TypeCon(..),
  TypePred(..),
  TypePredCon(..),
  TypeScheme(..),
  UnqualifiedType,
  FieldAccessor,
  ExtendedNatural(..),
  boolAsType,
  domainConstructors,
  extractFields,
  extractHeadVar,
  fvType,
  fvTypePred,
  fvTypeScheme,
  kindNatInType,
  splitFuncType,
  splitFuncTypeN,
  isFuncType,
  isListType,
  isUnitType,
  isPostStage,
  isPredAllowedImplicitly,
  mkCon,
  mkFunArgs,
  mkNoStage,
  mkNoDomain,
  mkPost,
  mkPre,
  mkKBool,
  mkTT,
  mkFF,
  mkProverDomain,
  mkPublic,
  mkPublicDomain,
  mkScheme,
  mkTVar,
  mkTApp,
  mkTCon,
  mkTypeBool,
  mkTypeBoolMod,
  mkTypeList,
  mkTypeArr,
  mkTypePubBool,
  mkTypePubUInt,
  mkTypeU64,
  mkNat,
  mkInfinite,
  mkQualified,
  mkQualifiedL,
  mkTypeString,
  mkTypeTuple,
  mkTypeUInt,
  mkTypeUIntMod,
  mkTypeUnit,
  mkUnqualUInt,
  mkUnqualBool,
  mkVerifierDomain,
  subType,
  subTypePred,
  subVarInType,
  typeToScheme,
  traverseTypeInTypePred,
  tryNegateTypePred,
  typeConIsInjective,
  typeConKind,
  typeGetVars,
  typeGetVarsWithLoc,
  typeSchemePredicates,
  typeSchemeQuantifiers,
  typeSchemeType,
  typesInTypePred,
  typeKind,
  applyKindFun,
  natLiteralsInType,
  selfInType,
  pattern PredSub,
  pattern PredStageSub,
  pattern PredDef,
  pattern PredQualify,
  pattern PredMutableVariable,
  pattern PredEq,
  pattern PredHasField,
  pattern PredPossibleInput,
  pattern PredConvertibleTo,
  pattern PredPre,
  pattern PredPost,
  pattern PredWireExpr,
  pattern PredAssertEq,
  pattern PredMutableComponent,
  pattern PredToString,
  pattern PredValidStore,
  pattern PredHasDefaultValue,
  pattern PredArray,
  pattern PredExtendedArithmetic,
  pattern PredSized,
  pattern PredField,
  pattern PredChallenge,
  pattern PredConvertible,
  pattern PredPermutationCheck,
  pattern PredVectors,
  pattern PredVectorization,
  pattern PredObliviousChoice,
  pattern PredTestExtendedArithmetic,
  pattern PredTestField,
  pattern PredTestChallenge,
  pattern PredTestConvertible,
  pattern PredTestPermutationCheck,
  pattern PredTestVectors,
  pattern PredTestObliviousChoice,
  pattern TQualify,
  pattern TUnit,
  pattern TString,
  pattern TDomain,
  pattern TStage,
  pattern TKBool,
  pattern THole,
  pattern TBool,
  pattern TUInt,
  pattern TNat,
  pattern TTuple,
  pattern TFun,
  pattern TGetUnqual,
  pattern TGetStage,
  pattern TGetDomain,
  pattern TCast,
  pattern TCastUnqual,
  pattern TCastStage,
  pattern TCastDomain,
  pattern TList,
  pattern TArr,
  pattern TStore,
)
where

import Basic.Location
import Support.Pretty
import Support.UniqMap
import Support.Unique
import Typing.Kind

import Control.Lens hiding (Level)
import Data.Maybe (mapMaybe)
import Data.List (intersperse)
import Data.Text (Text)
import GHC.Natural (Natural)
import GHC.Stack (HasCallStack)
import Control.Exception (ArithException(..), throw)
import Control.Arrow (first)

data SemiRing
  = Unspecified -- natural numbers in $pre, default modulus in $post
  | Mod         -- field of integers mod p
  deriving (Eq, Ord, Show)

instance Pretty SemiRing where
  pretty Unspecified = "Unspecified"
  pretty Mod = "Mod"

data ExtendedNatural
  = Finite !Natural
  | Infinite
  deriving (Show, Eq, Ord)

instance Num ExtendedNatural where
  Finite n + Finite m = Finite (n + m)
  _        + _        = Infinite

  Finite 0 * _        = Finite 0
  _        * Finite 0 = Finite 0
  Finite n * Finite m = Finite (n * m)
  _        * _        = Infinite

  abs n = n

  signum _ = Finite 1

  fromInteger = Finite . fromInteger

  negate (Finite n) = Finite $ negate n
  negate Infinite = throw Underflow

instance Pretty ExtendedNatural where
  pretty (Finite n) = pretty n
  pretty Infinite = "inf"

u64 :: ExtendedNatural
u64 = Finite (2 ^ 64)

data TypeCon
  = ConBool          -- bool[...]
  | ConFun           -- ... -> ...
  | ConList          -- list[...]
  | ConArr           -- arr[...]
  | ConNat ExtendedNatural   -- e.g. 2 in bool[2]
  | ConString        -- string
  | ConProver        -- @prover
  | ConPublic        -- @public
  | ConNoDomain      -- @? (missing domain produced by parser, handled by TC)
  | ConTuple Int     -- tuple[...]
  | ConUInt          -- uint[...]
  | ConUnit          -- ()
  | ConVerifier      -- @verifier
  | ConPre           --  $pre
  | ConPost          --  $post
  | ConNoStage       --  $? (missing stage produced by parser, handled by TC)
  | ConFF            -- ff (indicator of not being permitted in rhss of match expression)
  | ConTT            -- tt (indicator of being permitted in rhss of match expression)
  | ConNoBool
  | ConGetUnqual     -- getUnqual[T]
  | ConGetStage      -- getStage[T]
  | ConGetDomain     -- getDomain[T]
  | ConCast          -- Cast[Q, @D]
  | ConCastUnqual    -- CastUnqual[T, @D]
  | ConCastStage     -- CastStage[$S, @D]
  | ConCastDomain    -- CastDomain[@D1, @D]
  | ConQualify       -- T $S @D
  | ConStore         -- store[K, V]
  | ConHole          -- _
  deriving (Show, Eq, Ord)

typeConIsInjective :: TypeCon -> Bool
typeConIsInjective c = c `notElem` [ConGetUnqual, ConGetStage, ConGetDomain]

data Type a
  = TCon TypeCon Location
  | TVar a Kind Location
  | TSelf Location
  | TApp (Type a) [Type a] Location
  deriving (Ord, Functor, Foldable, Traversable)

natLiteralsInType :: Traversal' (Type a) Natural
natLiteralsInType f = \case
  TCon (ConNat (Finite n)) l -> TCon <$> (ConNat . Finite <$> f n) <*> pure l
  TApp t ts l -> TApp <$> natLiteralsInType f t <*> traverse (natLiteralsInType f) ts <*> pure l
  con@TCon{} -> pure con
  var@TVar{} -> pure var
  self@TSelf{} -> pure self

selfInType
  :: Applicative f
  => f (Type a) -> Type a -> f (Type a)
selfInType tself = \case
  tcon@TCon{} -> pure tcon
  TApp t ts l -> TApp <$> selfInType tself t <*> traverse (selfInType tself) ts <*> pure l
  tvar@TVar{} -> pure tvar
  TSelf{} -> tself

mkTVar :: HasLocation a => a -> Kind -> Type a
mkTVar x k = TVar x k (location x)

mkTApp :: Type a -> [Type a] -> Type a
mkTApp t [] = t
mkTApp t ts = TApp t ts (joinLocations (location t) (location (last ts)))

mkTCon :: TypeCon -> Type a
mkTCon con = TCon con NoLocation

instance Eq a => Eq (Type a) where
  TCon c _ == TCon c' _ = c == c'
  TVar x k _ == TVar x' k' _ = (x, k) == (x', k')
  TApp t ts _ == TApp t' ts' _ = (t, ts) == (t', ts')
  TSelf _ == TSelf _ = True
  _ == _ = False

-- Unchecked unqualified types.
-- If t :: UnqualifiedType a then t must have KindUnqualified.
type UnqualifiedType a = Type a

-- Unchecked domain types.
-- If d :: DomainType a then d must have KindDomain.
type DomainType a = Type a

-- Unchecked qualified types.
-- If t :: QualifiedType a then t must have KindStar.
type QualifiedType a = Type a

-- Unchecked stage types.
-- If s :: StageType a then s must have KindStage
type StageType a = Type a

-- Unchecked natural number types.
-- If m :: ModulusType a then m must have KindNat
type NatType a = Type a

-- For effect system
-- If m :: KBoolType a then m must have KindBool
type KBoolType a = Type a

boolAsType :: Bool -> KBoolType a
boolAsType b
  = TCon (if b then ConTT else ConFF) NoLocation

data GetInputFn
  = GetInstance
  | GetPublic
  | GetWitness
  deriving (Eq, Ord, Show)

type FieldAccessor = Either Int Text

data TypePredCon
  = PConSub -- @d1 <= @d2
  | PConStageSub --  $s1 <= $s2
  | PConDef -- default t1 = t2
  | PConQualify -- t can support d
  | PConMutableVariable -- variable of type t can be declared mutable
  | PConEq -- t1 = t2
  | PConHasField FieldAccessor -- tuple or structure has a component of given type
  | PConPossibleInput GetInputFn
  | PConConvertibleTo -- t1 can be converted to t2
  | PConPre -- s is $pre
  | PConPost -- s is $post
  | PConWitness -- t2 is the result of returning t1 in a witness expression
  | PConAssertEq -- t1 and t2 can be asserted to be equal
  | PConPrimType -- t is a primitive type (uint or bool)
  | PConPrimUint -- t is uint or uint[N]
  | PConPrimBool -- t is bool or bool[N]
  | PConPrimEq -- t1 and t2 are uint and bool with matching modulus
  | PConMutableComponent -- t can be element of a mutable list
  | PConValidStore -- store with key k, value v and stage s is well formed
  | PConToString
  | PConHasDefaultValue [FieldAccessor]
  | PConArray -- t is either list or array type constructor
  | PConSized
  | PConField
  | PConChallenge
  | PConConvertible
  | PConExtendedArithmetic
  | PConPermutationCheck
  | PConVectors
  | PConVectorization
  | PConObliviousChoice
  | PConTestField
  | PConTestChallenge
  | PConTestConvertible
  | PConTestExtendedArithmetic
  | PConTestPermutationCheck
  | PConTestVectors
  | PConTestObliviousChoice
  deriving (Eq, Ord, Show)

data TypePred a = TypePred
  { _predCon :: TypePredCon
  , _predArgs :: [Type a]
  , _predLocation :: Location
  }
  deriving (Ord, Functor, Foldable, Traversable)

pattern PredSub d1 d2 l = TypePred PConSub [d1, d2] l
pattern PredStageSub s1 s2 l = TypePred PConStageSub [s1, s2] l
pattern PredDef t1 t2 l = TypePred PConDef [t1, t2] l
pattern PredQualify t d l = TypePred PConQualify [t, d] l
pattern PredMutableVariable t l = TypePred PConMutableVariable [t] l
pattern PredEq t1 t2 l = TypePred PConEq [t1, t2] l
pattern PredHasField t1 sel t2 l = TypePred (PConHasField sel) [t1, t2] l
pattern PredPossibleInput f t s d l = TypePred (PConPossibleInput f) [t, s, d] l
pattern PredConvertibleTo t1 t2 l = TypePred PConConvertibleTo [t1, t2] l
pattern PredPre s l = TypePred PConPre [s] l
pattern PredPost s l = TypePred PConPost [s] l
pattern PredWireExpr shape from to l = TypePred PConWitness [shape, from, to] l
pattern PredAssertEq t1 t2 l = TypePred PConAssertEq [t1, t2] l
pattern PredMutableComponent d t l = TypePred PConMutableComponent [d, t] l
pattern PredToString t l = TypePred PConToString [t] l
pattern PredValidStore k v s l = TypePred PConValidStore [k, v, s] l
pattern PredHasDefaultValue path t l = TypePred (PConHasDefaultValue path) [t] l
pattern PredArray t l = TypePred PConArray [t] l
pattern PredSized t l = TypePred PConSized [t] l
pattern PredField n l = TypePred PConField [n] l
pattern PredChallenge n l = TypePred PConChallenge [n] l
pattern PredConvertible n1 n2 l = TypePred PConConvertible [n1, n2] l
pattern PredExtendedArithmetic l = TypePred PConExtendedArithmetic [] l
pattern PredPermutationCheck l = TypePred PConPermutationCheck [] l
pattern PredVectors l = TypePred PConVectors [] l
pattern PredVectorization l = TypePred PConVectorization [] l
pattern PredObliviousChoice l = TypePred PConObliviousChoice [] l
pattern PredTestField n l = TypePred PConTestField [n] l
pattern PredTestChallenge n l = TypePred PConTestChallenge [n] l
pattern PredTestConvertible n1 n2 l = TypePred PConTestConvertible [n1, n2] l
pattern PredTestExtendedArithmetic l = TypePred PConTestExtendedArithmetic [] l
pattern PredTestPermutationCheck l = TypePred PConTestPermutationCheck [] l
pattern PredTestVectors l = TypePred PConTestVectors [] l
pattern PredTestObliviousChoice l = TypePred PConTestObliviousChoice [] l

instance Eq a => Eq (TypePred a) where
  TypePred c ts _ == TypePred c' ts' _ = (c, ts) == (c', ts')

makeLensesFor [
    ("_predLocation", "locationInTypePred")
  ] ''TypePred

tryNegateTypePred :: TypePred a -> [TypePred a]
tryNegateTypePred (PredSub (TDomain TVProver) d l) = [PredSub d mkVerifierDomain l]
tryNegateTypePred (PredSub (TDomain TVVerifier) d l) = [PredSub d mkPublicDomain l]
tryNegateTypePred (PredSub d (TDomain TVPublic) l) = [PredSub mkVerifierDomain d l]
tryNegateTypePred (PredSub d (TDomain TVVerifier) l) = [PredSub mkProverDomain d l]
tryNegateTypePred (TypePred con ts l) = case con of
  PConPre  -> [TypePred PConPost ts l]
  PConPost -> [TypePred PConPre ts l]
  _        -> []

isPredAllowedImplicitly
  :: TypePred a -> Bool
isPredAllowedImplicitly (TypePred pcon _ _)
  = elem pcon 
    [ PConTestField
    , PConTestChallenge
    , PConTestConvertible
    , PConTestExtendedArithmetic
    , PConTestObliviousChoice
    , PConTestPermutationCheck
    , PConTestVectors
    ]

data TVDomain
  = TVPublic
  | TVVerifier
  | TVProver
  | TVNoDomain
  deriving (Eq, Ord)

data TVStage
  = TVPost
  | TVPre
  | TVNoStage
  deriving (Eq, Ord)

data TVKBool
  = TVFF
  | TVTT
  | TVNoBool
  deriving (Eq, Ord)

data Mutability
  = Mutable
  | Immutable
  deriving Eq

{-----------------------
 -- Type constructors --
 -----------------------}

domainConstructors :: [TypeCon]
domainConstructors = [ConProver, ConPublic, ConVerifier]

infixr 5 -*>
(-*>) :: Kind -> Kind -> Kind
k1 -*> k2 = k1 `KindFun` k2

typeConKind :: TypeCon -> Kind
typeConKind = \case
  ConBool -> KindNat -*> KindUnqualified
  ConList -> KindStar -*> KindUnqualified
  ConArr -> KindStar -*> KindUnqualified
  ConNat {} -> KindNat
  ConString -> KindUnqualified
  ConProver -> KindDomain
  ConPublic -> KindDomain
  ConNoDomain -> KindDomain
  ConTuple k -> foldr KindFun KindUnqualified (replicate k KindStar)
  ConUInt -> KindNat -*> KindUnqualified
  ConUnit -> KindUnqualified
  ConVerifier -> KindDomain
  ConFun -> KindStar -*> KindStar -*> KindUnqualified
  ConPre -> KindStage
  ConPost -> KindStage
  ConNoStage -> KindStage
  ConFF -> KindBool
  ConTT -> KindBool
  ConNoBool -> KindBool
  ConGetUnqual -> KindStar -*> KindUnqualified
  ConGetStage -> KindStar -*> KindStage
  ConGetDomain -> KindStar -*> KindDomain
  ConCast -> KindStar -*> KindDomain -*> KindStar
  ConCastUnqual -> KindUnqualified -*> KindDomain -*> KindUnqualified
  ConCastStage -> KindStage -*> KindDomain -*> KindStage
  ConCastDomain -> KindDomain -*> KindDomain -*> KindDomain
  ConQualify -> KindUnqualified -*> KindStage -*> KindDomain -*> KindStar
  ConStore -> KindUnqualified -*> KindUnqualified -*> KindUnqualified
  ConHole -> KindUnknown

typeKind :: Type a -> Kind
typeKind (TCon con _) = typeConKind con
typeKind (TVar _ k _) = k
typeKind (TSelf _) = KindStar
typeKind (TApp t ts _) = applyKindFun k ks
  where
    k = typeKind t
    ks = map typeKind ts

applyKindFun :: HasCallStack => Kind -> [Kind] -> Kind
applyKindFun k [] = k
applyKindFun (KindFun k1 k2) (k : ks) | k1 == k = applyKindFun k2 ks
applyKindFun _ _ = error "Ill formed kind."

{---------------------
 -- Type predicates --
 ---------------------}

instance Pretty GetInputFn where
  pretty GetInstance = "instance"
  pretty GetPublic = "public"
  pretty GetWitness = "witness"

instance Pretty a => Pretty (TypePred a) where
  pretty (PredSub a b _) = pretty a <+> "<=" <+> pretty b
  pretty (PredStageSub a b _) = pretty a <+> "<=" <+> pretty b
  pretty (PredDef a b _) = "default" <+> pretty a <+> "=" <+> pretty b
  pretty (PredQualify t d _) = "qualify" <+> pretty t <+> "with" <+> pretty d
  pretty (PredMutableVariable t _) = "MutableVariable" <> brackets (pretty t)
  pretty (PredEq t1 t2 _) = pretty t1 <+> "~" <+> pretty t2
  pretty (PredHasField t1 i t2 _) =
    parens (pretty t1) <> "." <> either pretty pretty i <+> "~" <+> pretty t2
  pretty (PredPossibleInput fn t s d _) =
    pretty fn <> "-input" <> brackets (hcat $ punctuate "," $ fmap pretty [t, s, d])
  pretty (PredConvertibleTo f t _) = pretty f <+> "convertible-to" <+> pretty t
  pretty (PredPre s _) = "Pre" <> brackets (pretty s)
  pretty (PredPost s _) = "Post" <> brackets (pretty s)
  pretty (PredWireExpr shape f t _) =
    "wire" <> parens (pretty shape <> "," <+> pretty f) <+> "->" <+> pretty t
  pretty (PredAssertEq t1 t2 _) = "assert-eq" <> brackets (hcat $ punctuate "," $ fmap pretty [t1, t2])
  pretty (PredMutableComponent d t _) = "MutableListElem" <> brackets (pretty d <> "," <> pretty t)
  pretty (PredToString t _) = "ToString" <> brackets (pretty t)
  pretty (PredHasDefaultValue path t _) -- TODO: I think this should be removed
    = "has-default-value" <> prettyPath path <> brackets (pretty t)
  pretty (PredArray t _) = "Array" <> brackets (pretty t)
  pretty (PredSized t _) = "Sized" <> brackets (pretty t)
  pretty (PredField t _) = "Field" <> brackets (pretty t)
  pretty (PredChallenge t _) = "Challenge" <> brackets (pretty t)
  pretty (PredConvertible t1 t2 _) = "Convertible" <> brackets (pretty t1 <> "," <> pretty t2)
  pretty (PredExtendedArithmetic _) = "ExtendedArithmetic"
  pretty (PredPermutationCheck _) = "PermutationCheck"
  pretty (PredVectors _) = "Vectors"
  pretty (PredVectorization _) = "Vectorization"
  pretty (PredObliviousChoice _) = "ObliviousChoice"
  pretty (TypePred con ts _) = pretty (show con) <> brackets (hcat $ punctuate "," (map pretty ts))

ppFieldAccessor :: FieldAccessor -> Doc ann
ppFieldAccessor (Left i) = pretty i
ppFieldAccessor (Right name) = pretty name

prettyPath :: [FieldAccessor] -> Doc ann
prettyPath xs = hcat (map go xs)
  where
    go y = "." <> ppFieldAccessor y

instance HasLocation (TypePred a) where
  type UnLocated (TypePred a) = TypePred a
  location = view locationInTypePred
  setLocation pred l = pred & locationInTypePred .~ l
  stripLocation = locationInTypePred .~ NoLocation

traverseTypeInTypePred :: Traversal (TypePred a) (TypePred b) (Type a) (Type b)
traverseTypeInTypePred f (TypePred con ts l) =
  (\ts' -> TypePred con ts' l) <$> traverse f ts

fvTypePred :: Uniquable a => TypePred a -> UniqMap a
fvTypePred = unionsUM . map fvType . typesInTypePred

-- | List all the types that occur in the type predicate
typesInTypePred :: TypePred a -> [Type a]
typesInTypePred = toListOf traverseTypeInTypePred

subTypePred :: Uniquable a => UniqMap (Type a) -> TypePred a -> TypePred a
subTypePred um = over traverseTypeInTypePred (subType um)

{----------------
 -- Data Types --
 ----------------}

locationInType :: Lens' (Type a) Location
locationInType f (TCon t l) = TCon t <$> f l
locationInType f (TVar x k l) = TVar x k <$> f l
locationInType f (TSelf l) = TSelf <$> f l
locationInType f (TApp t ts l)  = TApp t ts <$> f l

instance HasLocation (Type a) where
  type UnLocated (Type a) = Type a
  location = view locationInType
  setLocation t l = t & locationInType .~ l
  stripLocation = locationInType .~ NoLocation

instance Plated (Type a) where
  plate _ con@TCon{}       = pure con
  plate _ var@TVar{}       = pure var
  plate _ self@TSelf{}     = pure self
  plate f (TApp t ts l)    = TApp <$> f t <*> traverse f ts <*> pure l

varsInType :: Type a -> [a]
varsInType = map unLocated . typeGetVarsWithLoc

fvType :: Uniquable a => Type a -> UniqMap a
fvType = fromListUM . map (\x -> (x, x)) . varsInType

typeGetVarsWithLoc :: Type name -> [Located name]
typeGetVarsWithLoc t = para go t []
  where
    go (TVar n _ l) = const (Located l n :)
    go _            = foldr (.) id

typeGetVars :: Uniquable name => Type name -> [name]
typeGetVars = elemsUM . fromListUM' . map unLocated . typeGetVarsWithLoc

subVarInType :: Eq name => name -> Type name -> Type name -> Type name
subVarInType x t' = go
  where
    go t@(TVar y _ _) = if y == x then t' else t
    go (TApp t ts l)  = TApp (go t) (map go ts) l
    go t              = t

-- Type substitution:
subType :: Uniquable a => UniqMap (Type a) -> Type a -> Type a
subType um = transform replaceVar
  where
    replaceVar t@(TVar x _ _) = findWithDefaultUM t x um
    replaceVar t = t

isPostStage :: StageType a -> Bool
isPostStage (TStage TVPost) = True
isPostStage _               = False

isUnitType :: QualifiedType a -> Bool
isUnitType = go
  where
    go (TQualify t _ _) = go t
    go TUnit = True
    go _ = False

isListType :: QualifiedType a -> Bool
isListType = go
  where
    go (TQualify t _ _) = go t
    go TList{} = True
    go _ = False

isFuncType :: QualifiedType a -> Bool
isFuncType (TQualify t _ _) = isFuncType t
isFuncType TFun{} = True
isFuncType _ = False

splitFuncType :: QualifiedType a -> ([QualifiedType a], QualifiedType a)
splitFuncType = \case
  TQualify (TFun t1 t2) _ _ -> first (t1 :) $ splitFuncType t2
  TFun t1 t2 -> first (t1 :) $ splitFuncType t2
  t -> ([], t)

splitFuncTypeN :: HasCallStack => QualifiedType a -> Int -> ([QualifiedType a], QualifiedType a)
splitFuncTypeN t 0 = ([], t)
splitFuncTypeN _ n | n < 0 = error "Negative input"
splitFuncTypeN (TQualify t@TFun{} _ _) n = splitFuncTypeN t n
splitFuncTypeN (TFun t1 t2) n = first (t1 :) $ splitFuncTypeN t2 (n - 1)
splitFuncTypeN _ _ = error "Too few function arguments."

extractFields
  :: [TypePred a] -> [Type a]
extractFields
  = let
      getField (PredField n _)
        = Just n
      getField _
        = Nothing
    in
    mapMaybe getField

{--------------------------
 -- Convenient type view --
 --------------------------}

instance Pretty TVDomain where
  pretty TVPublic = "@public"
  pretty TVVerifier = "@verifier"
  pretty TVProver = "@prover"
  pretty TVNoDomain = "@?"

instance Pretty TVStage where
  pretty TVPre = "$pre"
  pretty TVPost = "$post"
  pretty TVNoStage = "$?"

instance Pretty TVKBool where
  pretty TVFF = "ff"
  pretty TVTT = "tt"
  pretty TVNoBool = "??"
  
viewDom :: TypeCon -> Maybe TVDomain
viewDom ConPublic = Just TVPublic
viewDom ConVerifier = Just TVVerifier
viewDom ConProver = Just TVProver
viewDom ConNoDomain = Just TVNoDomain
viewDom _ = Nothing

viewStage :: TypeCon -> Maybe TVStage
viewStage ConPre = Just TVPre
viewStage ConPost = Just TVPost
viewStage ConNoStage = Just TVNoStage
viewStage _ = Nothing

viewKBool :: TypeCon -> Maybe TVKBool
viewKBool ConFF = Just TVFF
viewKBool ConTT = Just TVTT
viewKBool ConNoBool = Just TVNoBool
viewKBool _ = Nothing

viewTBool :: Type a -> Maybe (Type a)
viewTBool (TApp (TCon ConBool _) [mod] _) = Just mod
viewTBool _ = Nothing

viewTUInt :: Type a -> Maybe (Type a)
viewTUInt (TApp (TCon ConUInt _) [mod] _) = Just mod
viewTUInt _ = Nothing

pattern TString <- TCon ConString _
pattern TDomain d <- TCon (viewDom -> Just d) _
pattern TStage s <- TCon (viewStage -> Just s) _
pattern TKBool b <- TCon (viewKBool -> Just b) _
pattern TUnit <- TCon ConUnit _
pattern THole <- TCon ConHole _
pattern TBool m <- (viewTBool -> Just m)
pattern TUInt m <- (viewTUInt -> Just m)
pattern TNat n <- TCon (ConNat n) _
pattern TList t <- TApp (TCon ConList _) [t] _
pattern TArr t <- TApp (TCon ConArr _) [t] _ where
  TArr t = TApp (TCon ConArr NoLocation) [t] NoLocation
pattern TTuple ts <- TApp (TCon (ConTuple _) _) ts _
pattern TFun t1 t2 <- TApp (TCon ConFun _) [t1, t2] _
pattern TGetUnqual t <- TApp (TCon ConGetUnqual _) [t] _ where
  TGetUnqual t = TApp (TCon ConGetUnqual NoLocation) [t] NoLocation
pattern TGetStage t <- TApp (TCon ConGetStage _) [t] _ where
  TGetStage t = TApp (TCon ConGetStage NoLocation) [t] NoLocation
pattern TGetDomain t <- TApp (TCon ConGetDomain _) [t] _ where
  TGetDomain t = TApp (TCon ConGetDomain NoLocation) [t] NoLocation
pattern TCast q d <- TApp (TCon ConCast _) [q, d] _ where
  TCast q d = TApp (TCon ConCast NoLocation) [q, d] NoLocation
pattern TCastUnqual t d <- TApp (TCon ConCastUnqual _) [t, d] _ where
  TCastUnqual t d = TApp (TCon ConCastUnqual NoLocation) [t, d] NoLocation
pattern TCastStage s d <- TApp (TCon ConCastStage _) [s, d] _ where
  TCastStage s d = TApp (TCon ConCastStage NoLocation) [s, d] NoLocation
pattern TCastDomain d1 d <- TApp (TCon ConCastDomain _) [d1, d] _ where
  TCastDomain d1 d = TApp (TCon ConCastDomain NoLocation) [d1, d] NoLocation
pattern TQualify u s d <- TApp (TCon ConQualify _) [u, s, d] _
pattern TStore k v <- TApp (TCon ConStore _) [k, v] _ where
  TStore k v = TApp (TCon ConStore NoLocation) [k, v] NoLocation

instance Pretty a => Pretty (Type a) where
  pretty = go never_prec
    where
      never_prec = 40
      fun_prec = 50
      stage_prec = 60
      always_prec = 1000
      goFun p t1 t2 = parensIf (p > fun_prec) $ go (fun_prec + 1) t1 <+> "->" <+> go fun_prec t2
      go p t = case t of
        TBool (TNat Infinite) -> "bool"
        TBool t -> "bool" <> brackets (pretty t)
        TString -> "string"
        TUInt (TNat Infinite) -> "uint"
        TUInt t -> "uint" <> brackets (pretty t)
        TUnit -> "()"
        THole -> "_"
        TVar x k _
          | k == KindStage  -> "$" <> pretty x
          | k == KindDomain -> "@" <> pretty x
          | otherwise -> pretty x
        TDomain d -> pretty d
        TStage s -> pretty s
        TKBool b -> pretty b
        TQualify (TFun t1 t2) _ _ -> goFun p t1 t2
        TFun t1 t2  ->  goFun p t1 t2
        TList t -> "list" <> brackets (pretty t)
        TArr t -> "arr" <> brackets (pretty t)
        TNat n -> pretty n
        TTuple ts -> "tuple" <> brackets (hsep $ punctuate comma $ map pretty ts)
        TQualify u s d -> parensIf (p > stage_prec) $ go (stage_prec + 1) u <+> go (stage_prec + 1) s <+> go (stage_prec + 1) d
        TGetUnqual t -> "getUnqual" <> brackets (pretty t)
        TGetStage t -> "getStage" <> brackets (pretty t)
        TGetDomain t -> "getDomain" <> brackets (pretty t)
        TCast q d -> "Cast" <> brackets (pretty q <> "," <+> pretty d)
        TCastUnqual t d -> "CastUnqual" <> brackets (pretty t <> "," <+> pretty d)
        TCastStage s d -> "CastStage" <> brackets (pretty s <> "," <+> pretty d)
        TCastDomain d1 d -> "CastDomain" <> brackets (pretty d1 <> "," <+> pretty d)
        TStore k v -> "store" <> brackets (pretty k <> "," <+> pretty v)
        TApp t ts _ -> go always_prec t <> brackets (hsep $ punctuate comma $ map pretty ts)
        TCon con _ -> pretty $ show con
        TSelf _ -> "Self"

extractHeadVar
  :: Type a -> Maybe (Located a)
extractHeadVar = \ case
  TQualify u        _ _
    -> extractHeadVar u
  TVar x            _ l
    -> Just (Located l x)
  TApp (TVar x _ l) _ _
    -> Just (Located l x)
  _ -> Nothing

kindNatInType :: Traversal' (Type a) (Type a)
kindNatInType f = \ case
  q@(TQualify u s _)
    | TStage TVPre       <- s -> pure q
    | TUInt (TNat _)     <- u -> f q
    | TBool (TNat _)     <- u -> f q
    | TUInt (TVar _ _ _) <- u -> f q
    | TBool (TVar _ _ _) <- u -> f q
  TApp tfun targs l    -> TApp <$> kindNatInType f tfun <*> traverse (kindNatInType f) targs <*> pure l
  t                    -> pure t

{------------------------
 -- Smart constructors --
 ------------------------}

mkCon :: TypeCon -> Type a
mkCon con = TCon con NoLocation

mkPre :: StageType a
mkPre = mkCon ConPre

mkPost :: StageType a
mkPost = mkCon ConPost

mkNoStage :: StageType a
mkNoStage = TCon ConNoStage NoLocation

mkNoDomain :: DomainType a
mkNoDomain = TCon ConNoDomain NoLocation

mkPublic :: UnqualifiedType a -> QualifiedType a
mkPublic t = mkQualified t mkPre mkPublicDomain

mkPublicDomain :: DomainType a
mkPublicDomain = mkCon ConPublic

mkVerifierDomain :: DomainType a
mkVerifierDomain = mkCon ConVerifier

mkProverDomain :: DomainType a
mkProverDomain = mkCon ConProver

mkKBool :: Bool -> KBoolType a
mkKBool b
  = if b then mkCon ConTT else mkCon ConFF

mkFF :: KBoolType a
mkFF = mkKBool False

mkTT :: KBoolType a
mkTT = mkKBool True

mkTypeBool :: StageType a -> DomainType a -> QualifiedType a
mkTypeBool = mkTypeBool' Nothing

mkTypeBoolMod :: NatType a -> StageType a -> DomainType a -> QualifiedType a
mkTypeBoolMod nat = mkTypeBool' (Just nat)

mkTypeBool' :: Maybe (NatType a) -> StageType a -> DomainType a -> QualifiedType a
mkTypeBool' maybeMod stage dom =
  mkScalarType maybeMod stage dom ConBool

mkTypeUInt :: StageType a -> DomainType a -> QualifiedType a
mkTypeUInt = mkTypeUInt' Nothing

mkTypeUIntMod :: NatType a -> StageType a -> DomainType a -> QualifiedType a
mkTypeUIntMod nat = mkTypeUInt' (Just nat)

mkTypeUInt' :: Maybe (NatType a) -> StageType a -> DomainType a -> QualifiedType a
mkTypeUInt' maybeMod stage dom =
  mkScalarType maybeMod stage dom ConUInt

mkTypeU64 :: StageType a -> DomainType a -> QualifiedType a
mkTypeU64 = mkTypeUIntMod (mkNat u64)

mkNat :: ExtendedNatural -> NatType a
mkNat n = mkCon (ConNat n)

mkInfinite :: NatType a
mkInfinite = mkNat Infinite

mkUnqualUInt :: NatType a ->  UnqualifiedType a
mkUnqualUInt t = TApp (mkCon ConUInt) [t] NoLocation

mkUnqualBool :: NatType a -> UnqualifiedType a
mkUnqualBool t = TApp (mkCon ConBool) [t] NoLocation

mkScalarType :: Maybe (NatType a) -> StageType a -> DomainType a ->
  TypeCon -> QualifiedType a
mkScalarType maybeMod stage dom con =
  mkQualified unqualifiedTy stage dom
  where
    unqualifiedTy = case maybeMod of
      Just mod -> mkTApp (mkCon con) [mod]
      Nothing -> mkTApp (mkCon con) [mkCon (ConNat Infinite)]

mkTypeList :: QualifiedType a -> DomainType a -> QualifiedType a
mkTypeList elemType = mkQualified (TApp (mkCon ConList) [elemType] NoLocation) mkPre

mkTypeArr :: QualifiedType a -> DomainType a -> QualifiedType a
mkTypeArr elemType = mkQualified (TApp (mkCon ConArr) [elemType] NoLocation) mkPre

mkTypeString :: QualifiedType a
mkTypeString = mkPublic $ mkCon ConString

mkTypeTuple :: [QualifiedType a] -> QualifiedType a
mkTypeTuple ts = mkPublic $ TApp (mkCon (ConTuple (length ts))) ts NoLocation

mkTypePubUInt :: QualifiedType a
mkTypePubUInt = mkTypeUInt (mkCon ConPre) (mkCon ConPublic)

mkTypePubBool :: QualifiedType a
mkTypePubBool = mkTypeBool (mkCon ConPre) (mkCon ConPublic)

mkTypeUnit :: QualifiedType a
mkTypeUnit =  mkQualified (mkCon ConUnit) (mkCon ConPre) (mkCon ConPublic)

mkQualified :: UnqualifiedType a -> StageType a -> DomainType a -> QualifiedType a
mkQualified u s d = mkQualifiedL u s d NoLocation

mkQualifiedL :: UnqualifiedType a -> StageType a -> DomainType a -> Location -> QualifiedType a
mkQualifiedL u s d l = TApp (TCon ConQualify l) [u, s, d] l

mkFunArgs :: [QualifiedType a] -> QualifiedType a -> QualifiedType a
mkFunArgs []       r = r
mkFunArgs (a : as) r = mkPublic (a `mkFun` mkFunArgs as r)
  where
    mkFun x y = TApp (TCon ConFun NoLocation) [x, y] NoLocation

{------------------
 -- Type schemes --
 ------------------}

data TypeScheme a
  = TForAll
  { _typeSchemeQuantifiers :: [a]
  , _typeSchemePredicates :: [TypePred a]
  , _typeSchemeType :: Type a
  }

makeLenses ''TypeScheme

mkScheme :: [a] -> [TypePred a] -> Type a -> TypeScheme a
mkScheme = TForAll

typeToScheme :: QualifiedType a -> TypeScheme a
typeToScheme = TForAll [] []

-- Currently we should only have type schemes with either no free variables or all
-- free variables. But in case this changes we want this function to operate
-- correctly.
fvTypeScheme :: Uniquable a => TypeScheme a -> UniqMap a
fvTypeScheme (TForAll xs ps t) =
  case xs of
    []  -> tyvars
    [x] -> deleteUM x tyvars
    _   -> tyvars `diffUM` fromListUM' xs
  where
    tyvars = unionsUM $ fvType t : map fvTypePred ps


instance Pretty a => Pretty (TypeScheme a) where
  pretty (TForAll vars preds t)
    | null vars, null preds = pretty t
    | null vars = prettyTypePreds <+> pretty t
    | null preds = prettyVars <+> pretty t
    | otherwise = prettyVars <+> prettyTypePreds <+> pretty t
    where
      prettyVars = pretty '∀' <> hsep (map pretty vars) <> "."
      prettyTypePreds =
        hcat (intersperse (space <> "&" <> space) $ map pretty preds) <+> "=>"

{-----------
 -- Level --
 -----------}

type Level = Int
