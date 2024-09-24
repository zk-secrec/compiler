{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Parser.Effect (
  EffectVar,
  Effect'(..),
  Effect,
  isDomain,
  isEmptyEffect,
  mkEffect,
  mkEffectEmpty,
  mkEffectMetaVar,
  wireEffect,
  isFFEff,
  eliminatePosts,
  removeStages,
  extractKBoolVars,
  effectGetVars,
  constrGetVars,
  tweGetVars,
  EffConstraint'(..),
  EffConstraint,
  TypeWithEffect'(..),
  TypeWithEffect,
  PolymorphicTypeWithEffect (..),
) where

import Basic.Location
import Basic.Var
import Support.Pretty
import Typing.Type

import Control.Lens
import Data.List
import GHC.Stack (HasCallStack)

type EffectVar = Var

--data Effect' a = Effect {
-- A hack to allow using Text instead of TyVar during parsing
-- but still allow the derived Functor and Foldable instances to work correctly with TyVar,
-- otherwise there was an infinite loop when effect checking Std.zksc.
data Effect' b a = Effect {
    _effectMetaVars :: [a],
    _effectPrims :: [Type b]
    --_effectPrims :: [Type TyVar]
    --_effectPrims :: [Type a] -- for some reason, this causes infinite loop when effect checking Std.zksc
  }
  deriving (Functor, Foldable)

instance (Pretty a, Pretty b) => Pretty (Effect' b a) where
--instance Pretty a => Pretty (Effect' a) where
  pretty (Effect vs ts) 
    = let 
        angled doc = "<" <> doc <> ">"
      in
      case (vs, ts) of
        ([], []) -> "ø"
        _        -> hcat $ punctuate " + " $ map pretty vs ++ map (angled.pretty) ts

type Effect = Effect' TyVar EffectVar
--type Effect = Effect' EffectVar

effectGetVars
  :: Effect -> [Var]
effectGetVars (Effect xs ts)
  = concat (xs : fmap typeGetVars ts)

mkEffectEmpty :: Effect' b a
--mkEffectEmpty :: Effect' a
mkEffectEmpty = Effect [] []

isEmptyEffect :: Effect' b a -> Bool
--isEmptyEffect :: Effect' a -> Bool
isEmptyEffect = \case
  Effect [] [] -> True
  _            -> False

mkEffectMetaVar :: a -> Effect' b a
--mkEffectMetaVar :: a -> Effect' a
mkEffectMetaVar x = Effect [x] []

mkEffect :: (Ord a, Ord b, Pretty b) => Type b -> Effect' b a
--mkEffect :: Ord a => Type TyVar -> Effect' a
--mkEffect :: Ord a => Type a -> Effect' a
mkEffect t@(TDomain _) = Effect [] [t]
mkEffect t@(TStage _) = Effect [] [t]
mkEffect t@(TKBool _) = Effect [] [t]
mkEffect (TQualify u s d) = mkEffect u <> mkEffect s <> mkEffect d
mkEffect t@(TGetUnqual _) = Effect [] [t]
mkEffect t@(TGetStage _) = Effect [] [t]
mkEffect t@(TGetDomain _) = Effect [] [t]
mkEffect (TList u) = mkEffect u
mkEffect (TArr u) = mkEffect u
mkEffect (TTuple ts) = mconcat (map mkEffect ts)
mkEffect (TUInt _) = mkEffectEmpty
mkEffect (TBool _) = mkEffectEmpty
mkEffect (TStore _ _) = mkEffectEmpty
mkEffect TString = mkEffectEmpty
mkEffect TUnit = mkEffectEmpty
mkEffect t@(TVar _ _ _) = Effect [] [t]
mkEffect t {- THole, TNat, TFun, TCast, TCastUnqual, TCastStage, TCastDomain -}
  = error ("mkEffect: Unexpected type " ++ render (pretty t))

wireEffect
  :: (Ord a, Ord b, Pretty b)
  => DomainType a -> Effect' b a
wireEffect d
  = mkEffect mkPost <> mkEffect (boolAsType (d /= mkVerifierDomain))

-- TODO: Optimize. Little bit inefficient.
mergeDedup :: (HasCallStack, Ord a) => [a] -> [a] -> [a]
mergeDedup xs ys = map head $ Data.List.group $ sort (xs ++ ys)

--isPublicDomain :: Type TyVar -> Bool
isDomain :: TVDomain -> Type a -> Bool
isDomain d (TDomain d') = d == d'
isDomain _ _            = False

isStage :: TVStage -> Type a -> Bool
isStage s (TStage s') = s == s'
isStage _ _           = False

isStageVar :: Type a -> Bool
isStageVar (TVar _ KindStage _) = True
isStageVar _                    = False

isKBool :: TVKBool -> Type a -> Bool
isKBool b (TKBool b') = b == b'
isKBool _ _           = False

isKBoolVar :: Type a -> Bool
isKBoolVar (TVar _ KindBool _) = True
isKBoolVar _                   = False

normalizeTypeList
  :: [Type a] -> [Type a]
normalizeTypeList ts
  | any (isDomain TVPublic) newts'
    = [mkPublicDomain] ++ filter ((== KindBool) . typeKind) newts'
  | otherwise
    = (if any (isDomain TVVerifier) newts then filter (not . isDomain TVProver) else id) .
      (if any (isStage TVPost) newts then filter (not . isStageVar) else id) $
      newts'
  where
    newts
      = filter (not . isDomain TVNoDomain) . filter (not . isStage TVPre) . filter (not . isKBool TVTT) $ ts
    newts'
      = (if any (isKBool TVFF) newts then filter (not . isKBoolVar) else id) $ 
        newts

-- Removes also boolean effects
-- Assumes normalized argument
removeStage
  :: [Type a] -> [Type a]
removeStage
  = filter (\ t -> let k = typeKind t in not (k == KindStage || k == KindBool))

-- Eliminates also boolean effects
eliminatePost
  :: [Type a] -> [Type a]
eliminatePost ts
  | any (isStage TVPost) ts'
    = [mkPublicDomain]
  | otherwise
    = ts'
  where
    ts' = filter ((/= KindBool) . typeKind) ts

isFFEff
  :: Effect' b a -> Bool
isFFEff (Effect _ es)
  = let
      isFF (TKBool TVFF)
        = True
      isFF _
        = False
    in
    any isFF es

extractKBoolVar
  :: [Type a] -> [Type a]
extractKBoolVar
  = filter isKBoolVar

instance (Ord a, Ord b) => Semigroup (Effect' b a) where
--instance Ord a => Semigroup (Effect' a) where
  Effect vs es <> Effect vs' es'
    = Effect vs'' (normalizeTypeList es'')
    where
      vs'' = mergeDedup vs vs'
      es'' = mergeDedup es es'

instance (Ord a, Ord b) => Monoid (Effect' b a) where
--instance Ord a => Monoid (Effect' a) where
  mempty = Effect [] []

typesInEffects
  :: (Functor f, Ord a, Ord b)
  => ([Type b] -> f [Type b]) -> [Effect' b a] -> f (Effect' b a)
typesInEffects f effs
  = let
      Effect xs ts
        = mconcat effs
    in
    Effect xs <$> f ts

removeStages
  :: (Ord a, Ord b)
  => [Effect' b a] -> Effect' b a
removeStages
  = typesInEffects %~ removeStage

eliminatePosts
  :: (Ord a, Ord b)
  => [Effect' b a] -> Effect' b a
eliminatePosts
  = typesInEffects %~ eliminatePost

extractKBoolVars
  :: (Ord a, Ord b)
  => [Effect' b a] -> Effect' b a
extractKBoolVars
  = typesInEffects %~ extractKBoolVar

data EffConstraint' b a
  = EffLe 
    { _constrEff1 :: Effect' b a
    , _constrEff2 :: Effect' b a
    , _constrLoc :: Location
    }
  | EffEq 
    { _constrEff1 :: Effect' b a
    , _constrEff2 :: Effect' b a
    , _constrLoc :: Location
    }
  | EffUnify
    { _constrTwe1 :: TypeWithEffect' b a
    , _constrTwe2 :: TypeWithEffect' b a
    , _constrLoc :: Location
    }
  deriving (Functor, Foldable)

instance (Pretty a, Pretty b) => Pretty (EffConstraint' b a) where
  pretty = \case
    EffLe e1 e2 l -> pretty e1 <+> "⊇" <+> pretty e2 <+> "//" <+> pretty l
    EffEq e1 e2 l -> pretty e1 <+> "~" <+> pretty e2 <+> "//" <+> pretty l
    EffUnify t1 t2 l -> pretty t1 <+> "=" <+> pretty t2 <+> "//" <+> pretty l

instance HasLocation (EffConstraint' b a) where
  type UnLocated (EffConstraint' b a) = EffConstraint' b a
  location = \case
    EffLe _ _ l -> l
    EffEq _ _ l -> l
    EffUnify _ _ l -> l
  setLocation (EffLe e1 e2 _) l = EffLe e1 e2 l
  setLocation (EffEq e1 e2 _) l = EffEq e1 e2 l
  setLocation (EffUnify t1 t2 _) l = EffUnify t1 t2 l
  stripLocation ec = ec

-- Simplified version of Type that has effect annotations with functional types.
data TypeWithEffect' b a
  = TweAny -- uint, bool, rigid type variable, anything that does not contain functions
  | TweTuple  -- [t1, ..., tn]
    { _tweCompTwes :: [TypeWithEffect' b a]
    }
  -- | TweTuple [TypeWithEffect' a] -- [t1, ..., tn]
  | TweFun   -- t1 -> t2 ! e [c1,c2,...,cn]
    { _tweArg     :: TypeWithEffect' b a
    , _tweRet     :: TypeWithEffect' b a
    , _tweEff     :: Effect' b a
    , _tweConstrs :: [EffConstraint' b a]
    }
  -- | TweFun (TypeWithEffect' a) (TypeWithEffect' a) (Effect' a) -- t1 -> t2 ! e
  deriving (Functor, Foldable)

makeLensesFor 
  [ ("_constrEff1", "constrEff1")
  , ("_constrEff2", "constrEff2")
  , ("_constrTwe1", "constrTwe1")
  , ("_constrTwe2", "constrTwe2")
  ] ''EffConstraint'

makeLensesFor
  [ ("_tweCompTwes", "tweCompTwes")
  , ("_tweArg", "tweArg")
  , ("_tweRet", "tweRet")
  , ("_tweEff", "tweEff")
  , ("_tweConstrs", "tweConstrs")
  ] ''TypeWithEffect'

instance (Pretty a, Pretty b) => Pretty (TypeWithEffect' b a) where
--instance Pretty a => Pretty (TypeWithEffect' a) where
  pretty = go never_prec
    where
      never_prec = 40
      fun_prec = 50
      goFun p t1 t2 eff cs = parensIf (p > fun_prec) $ (case eff of
          Effect [] [] -> go (fun_prec + 1) t1 <+> "->" <+> go fun_prec t2
          _            -> go (fun_prec + 1) t1 <+> "->" <+> go fun_prec t2 <+> "!" <+> pretty eff
        ) <> (if null cs then "" else " where" <+> pretty cs)
      go p = \case
        TweAny -> "*"
        TweTuple ts -> brackets $ hcat $ punctuate "," (map pretty ts)
        TweFun t1 t2 eff cs -> goFun p t1 t2 eff cs

data PolymorphicTypeWithEffect a = PolyTwe [a] (TypeWithEffect' a a)

instance Pretty a => Pretty (PolymorphicTypeWithEffect a) where
  pretty (PolyTwe es funTy) =
    let
      forallDoc = if null es then "" else "∀" <+> hcat (punctuate " " (map pretty es)) <+> ". "
    in
      forallDoc <> pretty funTy

type EffConstraint = EffConstraint' TyVar EffectVar
--type EffConstraint = EffConstraint' EffectVar

type TypeWithEffect = TypeWithEffect' TyVar EffectVar
--type TypeWithEffect = TypeWithEffect' TyVar

constrGetVars
  :: EffConstraint -> [Var]
constrGetVars constr@EffLe{}
  = concatMap effectGetVars $ 
    constr ^.. (constrEff1 <> constrEff2)
constrGetVars constr@EffEq{}
  = concatMap effectGetVars $
    constr ^.. (constrEff1 <> constrEff2)
constrGetVars constr@EffUnify{}
  = concatMap tweGetVars $
    constr ^.. (constrTwe1 <> constrTwe2)

tweGetVars
  :: TypeWithEffect -> [Var]
tweGetVars TweAny
  = []
tweGetVars twe@TweTuple{}
  = concatMap tweGetVars $
    twe ^. tweCompTwes
tweGetVars twe@TweFun{}
  = twe ^. tweArg . to tweGetVars ++
    twe ^. tweRet . to tweGetVars ++
    twe ^. tweEff . to effectGetVars ++
    twe ^. tweConstrs . to (concatMap constrGetVars)

