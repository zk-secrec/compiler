{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Typing.ConstraintSolver(
  TypePreds,
  TypeSubs,
  tcSimplifyConstraints,
  tcCheckConstr,
  tcReportUnsolved,
  simpType
) where

import Basic.Location
import Basic.Var
import Control.Lens (transform)
import Control.Monad
import Data.Either (isRight, isLeft)
import Data.Graph
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Semigroup
import Data.Text (Text)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Support.Pretty
import Support.UniqMap
import Typing.Constraints
import Typing.StructEnv
import Typing.TcM
import Typing.Type

{----------------------------------------------
 - Solving and simplifying constraint systems -
 ----------------------------------------------}

type TypePreds = [TypePred Var]

type Given = TypePred Var

type ExpandedGiven = TypePred Var

type Givens = [Given]

type ExpandedGivens = [ExpandedGiven]

data DomNode
  = DomPublic
  | DomVerifier
  | DomProver
  | DomVar TyVar
  deriving (Eq, Ord)

type DomRel = (DomNode, DomNode)

domTypeToDomNode :: DomainType Var -> Maybe DomNode
domTypeToDomNode t = case t of
  TDomain TVPublic -> Just DomPublic
  TDomain TVVerifier  -> Just DomVerifier
  TDomain TVProver  -> Just DomProver
  TVar x k _ | k == KindDomain -> Just (DomVar x)
  _ -> Nothing

domNodeToDomType :: DomNode -> DomainType Var
domNodeToDomType = \case
  DomPublic -> mkPublicDomain
  DomVerifier -> mkVerifierDomain
  DomProver -> mkProverDomain
  DomVar x -> TVar x KindDomain NoLocation

-- TODO: lossy information...
domRelToTypePred :: DomRel -> TypePred Var
domRelToTypePred (n1, n2) = PredSub t1 t2 NoLocation
  where
    t1 = domNodeToDomType n1
    t2 = domNodeToDomType n2

snub :: Ord a => [a] -> [a]
snub = Set.toList . Set.fromList

-- Expand given sub constraints using following facts:
-- @public <= *
-- * <= @prover
-- @a <= @b /\ @b <= @c -> @a <= @c
-- TODO: we don't really need to track of "trivial facts" like @public <= @* <= @prover
-- as those are eliminated elsewhere
transitiveClosureDomSubs :: [DomRel] -> [DomRel]
transitiveClosureDomSubs givens = snub [(pam v1, pam v2) | v1 <- [0 .. vertCount - 1], v2 <- reachable gr v1]
  where
    nodes = snub $ DomPublic : DomVerifier : DomProver : [n | p <- givens, n <- [fst p, snd p]]
    vertsMap = Map.fromList $ zip nodes [0..]
    pam = (Map.!) (Map.fromList $ zip [0..] nodes)
    vertCount = Map.size vertsMap
    givens' = snub $ givens ++ map (DomPublic,) nodes ++ map (,DomProver) nodes
    gr = buildG (0, vertCount - 1) [(vertsMap Map.! n1, vertsMap Map.! n2) | (n1, n2) <- givens']

selectDomSubs :: Givens -> ([DomRel], Givens)
selectDomSubs = go [] [] -- [p | pred <- preds, Just p <- [selectDomSub pred]]
  where
    go ns gs [] = (ns, gs)
    go ns gs (PredSub d1 d2 _ : ps)
      | Just n1 <- domTypeToDomNode d1, Just n2 <- domTypeToDomNode d2
        = go ((n1, n2) : ns) gs ps
    go ns gs (p : ps) = go ns (p : gs) ps

-- Agressively expand givens until closure.
-- This allows us to directly match predicates one-by-one.
expandGivens :: Givens -> ExpandedGivens
expandGivens givens = map domRelToTypePred subs' ++ givens'
  where
    (subs, givens') = selectDomSubs givens
    subs' = transitiveClosureDomSubs subs

-- Check if a predicate can be implied by an expanded predicate.
impliedByGiven :: TypePred Var -> ExpandedGiven -> Bool
impliedByGiven p (PredPre y _) = case p of
  PredPre x _ -> x == y
  PredEq (TStage TVPre) (TCastStage x _) _ -> x == y
  PredEq (TCastStage x _) (TStage TVPre) _ -> x == y
  PredEq z (TCastStage x _) _ -> x == y && z == y
  PredEq (TCastStage x _) z _ -> x == y && z == y
  PredEq (TStage TVPre) x _ -> x == y
  PredEq x (TStage TVPre) _ -> x == y
  PredConvertibleTo (TQualify (TUInt _) x _) (TUInt _) _ -> x == y
  _ -> False
impliedByGiven p (PredPost y _) = case p of
  PredPost x _ -> x == y
  PredEq (TStage TVPost) x _ -> x == y
  PredEq x (TStage TVPost) _ -> x == y
  _ -> False
impliedByGiven (PredEq d1 d2 l) p
  | TDomain TVProver <- d1 = impliedByGiven (PredSub d1 d2 l) p
  | TDomain TVProver <- d2 = impliedByGiven (PredSub d2 d1 l) p
  | TDomain TVPublic <- d1 = impliedByGiven (PredSub d2 d1 l) p
  | TDomain TVPublic <- d2 = impliedByGiven (PredSub d1 d2 l) p
impliedByGiven (PredSub d1 d2 _) (PredSub d1' d2' _) =
  d1 == d1' && d2 == d2'
impliedByGiven (PredPostRing r _) (PredPostRing r' _) = r == r'
impliedByGiven (PredSized t _) (PredSized t' _) = t == t'
impliedByGiven (PredArray t _) (PredArray t' _) = t == t'
impliedByGiven (PredChallenge r _) (PredChallenge r' _) = r == r'
impliedByGiven (PredConvertibleTo (TQualify (TInt r1) _ _) (TInt r2) _) (PredPostConvertible r1' r2' _) = r1 == r1' && r2 == r2'
impliedByGiven (PredConvertibleTo (TQualify (TBin r1) _ _) (TBin r2) _) (PredPostConvertible r1' r2' _) = r1 == r1' && r2 == r2'
impliedByGiven (PredPostConvertible r1 r2 _) (PredPostConvertible r1' r2' _) = r1 == r1' && r2 == r2'
impliedByGiven (PredExtendedArithmetic _) (PredExtendedArithmetic _) = True
impliedByGiven (PredPermutationCheck _) (PredPermutationCheck _) = True
impliedByGiven (PredVectors _) (PredVectors _) = True
impliedByGiven (PredVectorization _) (PredVectorization _) = True
impliedByGiven (PredObliviousChoice _) (PredObliviousChoice _) = True
impliedByGiven (PredTestPostRing r _) (PredPostRing r' _) = r == r'
impliedByGiven (PredTestPostConvertible r1 r2 _) (PredPostConvertible r1' r2' _) = r1 == r1' && r2 == r2'
impliedByGiven (PredTestChallenge r _) (PredChallenge r' _) = r == r'
impliedByGiven (PredTestExtendedArithmetic _) (PredExtendedArithmetic _) = True
impliedByGiven (PredTestPermutationCheck _) (PredPermutationCheck _) = True
impliedByGiven (PredTestVectors _) (PredVectors _) = True
impliedByGiven (PredTestObliviousChoice _) (PredObliviousChoice _) = True
impliedByGiven _ _ = False

-- TODO: We shouldn't be having to search through all expanded givens.
-- For example for stage predicates we know for a fact that domain <= givens don't help us.
isImpliedBySomeGiven :: TypePred Var -> ExpandedGivens -> Bool
isImpliedBySomeGiven p = any (impliedByGiven p)

-- Map from MetaTyVar to TyVar
type TypeSubs = UniqMap (Type TyVar)

flattenWanted :: WantedConstraints -> [TypePred TyVar]
flattenWanted (WantedConstraints ps is) = ps ++ concatMap flattenImplication is

flattenImplication :: Implication -> [TypePred TyVar]
flattenImplication Implication{..} = flattenWanted _implWanted

tcSimplifyConstraints :: Givens -> TcM (TypePreds, TypeSubs, UniqMap Var)
tcSimplifyConstraints givens = do
  continueRef <- newRef False
  let
    eliminate :: Level -> TypePreds -> TcM TypePreds
    eliminate _ [] = return []
    eliminate level (w : ws) = do
      w' <- subPred w
      elim <- tryElimPred w' level
      case elim of
        Delay -> (w':) <$> eliminate level ws
        Split ws' -> do
          tcDebugPrint $ if null ws'
            then "Elim " <+> pretty w'
            else "Split" <+> pretty w' <+> "into:" $$ indent 2 (vcat $ map pretty ws')
          writeRef continueRef True
          eliminate level (ws' ++ ws)

    loop :: Givens -> Level -> WantedConstraints -> TcM WantedConstraints
    loop givens level (WantedConstraints wanted implications) = tcWithLevel level $ do
      writeRef continueRef False
      wanted' <- eliminate level wanted
      b <- readRef continueRef
      if b
        then loop givens level (WantedConstraints wanted' implications)
        else do
          let givens' = expandGivens givens
          let wanted'' = [w | w <- wanted', not (w `isImpliedBySomeGiven` givens')]
          implications' <- forM implications $ \Implication{..} -> do
            wc' <- loop (givens ++ _implGiven) _implLevel _implWanted
            return $ Implication _implLevel _implGiven wc'
          return $ WantedConstraints wanted'' implications'
  wc0 <- tcTakeConstraints
  tcDebugPrint $ "Attempting to solve:" $$ indent 2 (pretty wc0) $$ "Using givens:" $$ indent 2 (pretty givens)
  initLevel <- tcGetLevel
  wc <- loop givens initLevel wc0
  tcDebugPrint $ "Solution:" $$ indent 2 (pretty wc)
  subs <- tcTakeSubs
  unsolved <- tcTakeUnsolved
  let (unsolvedStageVars, unsolved') = partitionUM ((== KindStage) . tyVarKind) unsolved
  mapM_ tcReportUnsolved unsolved'
  return (flattenWanted wc, subs, unsolvedStageVars)

tcReportUnsolved :: MetaTyVar -> TcM ()
tcReportUnsolved x = tcSetLoc (location x) $
    tcAddErr $ "Failed to infer type variable of kind \'" <> suffix <> "\'."
  where
    suffix = pretty (tyVarKind x)

subPred :: TypePred Var -> TcM (TypePred Var)
subPred = traverseTypeInTypePred tcSubType

data ElimResult
  = Delay               -- Delay elimination
  | Split TypePreds     -- Split a single equation to some simpler set of equations.

instance Semigroup ElimResult where
  Delay <> _ = Delay
  _ <> Delay = Delay
  Split ps <> Split qs = Split (ps <> qs)

mkRemove :: ElimResult
mkRemove = Split []

-- Tries to eliminate or simplify given predicate.
-- Elimination may fail in what case subsequent iteration can try again.
-- If entire system is delayed the system is considered solved/simplified.
tryElimPred :: TypePred Var -> Level -> TcM ElimResult
tryElimPred tp@(TypePred _ _ l) level = case tp of
  PredDef t1 t2 _ -> return $ tryElimDefault t1 t2
  PredSub t1 t2 _ -> return $ tryElimDomainLe t1 t2 l level
  PredQualify t d _ -> return $ tryElimQualify t d
  PredMutableVariable t _ -> tcSetLoc l $ tryElimMutableVariable t l
  PredEq t1 t2 _ -> tryElimEq t1 t2 l level
  PredHasField t1 i t2 _ -> tryElimHasField t1 i t2 l
  PredPossibleInput fn t s d _ -> return $ tryElimPossibleInput fn t s d l
  PredConvertibleTo t1 t2 _ -> return $ tryElimConvertibleTo t1 t2 l
  PredPre s _ -> return $ tryElimPre s
  PredPost s _ -> return $ tryElimPost s
  PredWireExpr shape from to _ -> tryElimWire shape from to l
  PredAssertEq t1 t2 _ -> return $ tryElimAssertEq t1 t2 l
  PredMutableComponent d t _ -> tryElimMutableComponent d t l
  PredToString t l -> return $ tryElimToString t l
  PredValidStore k v s l -> return $ tryElimValidStore k v s l
  PredHasDefaultValue path t l -> tryElimHasDefaultValue path t l
  PredArray t l -> return $ tryElimArray t l
  PredSized t l -> tryElimSized t l
  PredPostRing r _ -> return $ tryElimPostRing r
  PredPostConvertible r1 r2 _ -> return $ tryElimPostConvertible r1 r2
  PredChallenge r _ -> return $ tryElimChallenge r
  PredExtendedArithmetic _ -> return $ tryElimExtendedArithmetic
  PredPermutationCheck _ -> return $ tryElimPermutationCheck
  PredVectors _ -> return $ tryElimVectors
  PredVectorization _ -> return $ tryElimVectorization
  PredObliviousChoice _ -> return $ tryElimObliviousChoice
  PredTestPostRing _ _ -> return $ Delay
  PredTestPostConvertible _ _ _ -> return $ Delay
  PredTestChallenge _ _ -> return $ Delay
  PredTestExtendedArithmetic _ -> return $ Delay
  PredTestPermutationCheck _ -> return $ Delay
  PredTestVectors _ -> return $ Delay
  PredTestObliviousChoice _ -> return $ Delay
  _ -> tcFatal $ "ICE: Unhandled or ill formed type predicate:" <+> pretty tp

tryElimPost :: Type Var -> ElimResult
tryElimPost (TStage TVPost) = mkRemove
tryElimPost _               = Delay

tryElimPre :: Type Var -> ElimResult
tryElimPre (TStage TVPre) = mkRemove
tryElimPre _              = Delay

tryElimSized :: QualifiedType Var -> Location -> TcM ElimResult
tryElimSized q l
  = tcSetLoc l $ go q
  where
    go (TQualify t _ _)         = go t
    go TUnit                    = return mkRemove
    go TBin{}                   = return mkRemove
    go TInt{}                   = return mkRemove
    go (TTuple ts)              = foldr (<>) mkRemove <$> traverse go ts
    go (TApp (TVar x _ _) ts _) = goStruct x ts
    go (TVar x _ _)             = goStruct x []
    go (TSelf l)                = goSelf l
    go _                        = return Delay

    goStruct x ts = do
      msenv <- tcLookupStruct (varName x)
      case msenv of
        Nothing -> return Delay -- could still be resolved by givens
        Just StructEnv{..} -> do
          let TForAll vs _ _ = _structType
          let sub = fromListUM $ zip vs ts
          let fieldTypes = fmap (subType sub . _fieldType) (Map.elems _structFields)
          foldr (<>) mkRemove <$> traverse go fieldTypes

    goSelf l = do
      maybeself <- tcGetSelfType
      case maybeself of
        Just self -> go self
        _         -> tcSetLoc l $ tcThrowErr "Self type undefined."

tryElimPostRing :: RingType Var -> ElimResult
tryElimPostRing _ = Delay

tryElimPostConvertible :: RingType Var -> RingType Var -> ElimResult
tryElimPostConvertible m m'
  | m == m'
    = mkRemove
  | otherwise
    = Delay

tryElimChallenge :: NatType Var -> ElimResult
tryElimChallenge _ = Delay

tryElimExtendedArithmetic :: ElimResult
tryElimExtendedArithmetic = Delay

tryElimPermutationCheck :: ElimResult
tryElimPermutationCheck = Delay

tryElimVectors :: ElimResult
tryElimVectors = Delay

tryElimVectorization :: ElimResult
tryElimVectorization = Delay

tryElimObliviousChoice :: ElimResult
tryElimObliviousChoice = Delay

tryElimConvertibleTo :: Type Var -> UnqualifiedType Var -> Location -> ElimResult
tryElimConvertibleTo t1 t2 l = go (simpType t1) (simpType t2)
  where
    go (TQualify (TBin r) _ _) (TInt r')
      | r == r'
        = mkRemove
    go (TQualify (TInt r) s _) (TInt r')
      = helper s r r' l
    go (TQualify (TBin r) s _) (TBin r')
      = helper s r r' l
    go _                         _
      = Delay
    helper s r r' l
      | r == r'
        = mkRemove
      | otherwise
        = case s of
            TStage TVPre
              -> mkRemove
            TStage TVPost
              -> Split [PredPostConvertible r r' l]
            _ -> Delay
        
tryElimHasField :: Type Var -> Either Int Text -> Type Var -> Location -> TcM ElimResult
tryElimHasField t1 s t2 l = tcSetLoc l $ go (simpType t1)
  where
    go (TTuple ts)
      | isRight s = tcThrowErr "Tuple can not be indexed by name."
      | i < 0 || i >= length ts = tcThrowErr invalidIndexMsg
      | otherwise = return $ Split [PredEq (ts !! i) t2 l]
      where Left i = s
    go (TVar x _ _) = goStruct x []
    go (TQualify t _ _) = go (simpType t)
    go (TApp (TVar x _ _) ts _) = goStruct x ts
    go _ = return Delay

    goStruct x ts = do
      msenv <- tcLookupStruct (varName x)
      case msenv of
        Nothing -> return Delay -- could still be resolved by givens
        Just _ | isLeft s -> tcThrowErr structWithIndexMsg
        Just StructEnv{..} -> do
          let Right fname = s
          case Map.lookup fname _structFields of
            Nothing -> tcThrowErr $ noSuchFieldMsg x fname
            Just StructFieldInfo{..} -> do
              let TForAll vs _ _ = _structType
              let sub = fromListUM $ zip vs ts
              let fieldTy = subType sub _fieldType
              return $ Split [PredEq fieldTy t2 l]

    indDoc = parens (either pretty pretty s)
    structWithIndexMsg = "Structure can not be accessed by index."
    noSuchFieldMsg x fname = "Structure" <+> pretty x <+> "has no field" <+> pretty fname <> "."
    invalidIndexMsg = "Cannot select component" <+> indDoc <+> "from" <+> pretty t1 <> "."

-- TODO: no idea how defaulting should work tbh
-- Currently eliminate this predicate when the variable has been substituted.
tryElimDefault :: Type Var -> Type Var -> ElimResult
tryElimDefault (TVar x _ _) _ | isMetaTyVar x = Delay
tryElimDefault _ _ = mkRemove

tryElimMutableVariable :: Type Var -> Location -> TcM ElimResult
tryElimMutableVariable t l = tryElimMutableComponent d t l
  where d = mkPublicDomain `setLocation` l

-- Check if type t can be mutable component in context of domain d.
tryElimMutableComponent :: DomainType Var -> QualifiedType Var -> Location -> TcM ElimResult
tryElimMutableComponent d t l = go t
  where
    go (TQualify t s d')        = goQ t s d'
    go (TVar x _ _) | isTyVar x = return mkRemove
    go _                        = return Delay

    goQ (TVar x _ _) s _ | isTyVar x = return $ goPrim s
    goQ (TGetUnqual t) _ _ = go t
    goQ TUInt{} s _ = return $ goPrim s
    goQ TBool{} s _ = return $ goPrim s
    goQ (TInt (TBitwise{})) s _ = return $ goPrim s
    goQ (TBin (TBitwise{})) s _ = return $ goPrim s
    goQ TString{} s _ = return $ goPre s -- TODO: String could already be assumed to be $pre?
    goQ TUnit{} _ _ = return mkRemove
    goQ (TList t) s d' = return $ Split [PredMutableComponent d' t l] <> goPre s
    goQ (TArr t) s d' = return $ Split [PredMutableComponent d' t l] <> goPre s
    goQ (TStore _ _) s _ = return $ goPrim s -- TODO: This is iffy...
    goQ _ s d' = do
      senv <- tcGetStructsEnv
      return $ case tryGetFieldTypes senv t of
        Nothing -> Delay
        Just ts -> Split [PredMutableComponent d' t l | t <- ts] <> goPre s

    goPre s = Split [PredEq s (mkPre `setLocation` l) l]

    goPrim _ | TDomain TVPublic <- d = mkRemove
    goPrim (TStage TVPre) = mkRemove
    goPrim (TStage TVPost) = Split [PredEq d (mkPublicDomain `setLocation` l) l]
    goPrim _ = Delay

tryElimQualify :: UnqualifiedType Var -> DomainType Var -> ElimResult
tryElimQualify TUInt{} _ = mkRemove -- uint can have any domain
tryElimQualify TBool{} _ = mkRemove -- bool can have any domain
tryElimQualify _ (TDomain TVPublic) = mkRemove -- anything can have public domain
tryElimQualify _ _ = Delay

-- Idea behind AssertEq constraint is:
--    t1 = uint*, t2 = uint*
--    t2 = bool*, t2 = bool*
--    mixing bool and uint is not allowed
-- class AssertEq t1 t2 where
--    assert_eq :  t1 $post @d -> t2 $post @d -> unit $pre @d
tryElimAssertEq :: UnqualifiedType Var -> UnqualifiedType Var -> Location -> ElimResult
tryElimAssertEq (TUInt m) (TUInt n) l = Split [predField m l, predField n l]
tryElimAssertEq (TBool m) (TBool n) l = Split [predField m l, predField n l]
tryElimAssertEq _         _         _ = Delay

tryElimToString :: UnqualifiedType Var -> Location -> ElimResult
tryElimToString t l = go (simpType t)
  where
    tryElimToString' t = tryElimToString t l

    go (TQualify t s _) = tryElimToString' t <> Split [PredEq s mkPre l]
    go TBin{}           = mkRemove
    go TInt{}           = mkRemove
    go TString{}        = mkRemove
    go (TTuple t)       = sconcat $ mkRemove :| fmap tryElimToString' t
    go (TList t)        = tryElimToString' t
    go (TArr t)         = tryElimToString' t
    go _                = Delay

tryElimArray :: Type Var -> Location -> ElimResult
tryElimArray t _ = go (simpType t)
  where
    go (TQualify t _ _) = go t
    go (TCon ConList _) = mkRemove
    go (TCon ConArr _)  = mkRemove
    go _                = Delay

data KeyOrVal = IsKey | IsVal

-- Checks if store constructor {# k => v } produces a valid store of a
-- given stage. It's important that domains of k and v are in agreement with
-- the store domain. We don't check this here.
tryElimValidStore
  :: UnqualifiedType Var -> UnqualifiedType Var -> StageType Var -> Location
  -> ElimResult
tryElimValidStore k v s loc = go k v s
  where
    go (TUInt m) (TUInt m') _ | m == m' = mkRemove
    go (TUInt m) (TBool m') _ | m == m' = mkRemove
    go k v (TStage TVPre) = preKV IsKey k <> preKV IsVal v
    go _ _ _ = Delay

    preKV c (TQualify u s _) = preKV c u <> Split [PredEq s mkPre loc]
    preKV c (TTuple ts) = foldr (\t r -> preKV c t <> r) mkRemove ts
    preKV c (TList t) = preKV c t
    preKV c (TArr t) = preKV c t
    preKV _ TString = mkRemove
    preKV _ TUInt{} = mkRemove
    preKV _ TBool{} = mkRemove
    preKV _ TUnit = mkRemove
    preKV IsVal TStore{} = mkRemove
    preKV IsVal TFun{} = mkRemove
    preKV _ _ = Delay

tryElimHasDefaultValue :: [FieldAccessor] -> Type Var -> Location -> TcM ElimResult
tryElimHasDefaultValue p t l = go t
  where
    go (TQualify t _ _) = go t
    go (TVar x _ _) = goStruct x []
    go (TApp (TVar x _ _) ts _) = goStruct x ts
    go TUnit{} = return mkRemove
    go TUInt{} = return mkRemove
    go TBool{} = return mkRemove
    go TStore{} = return mkRemove
    go TString = return mkRemove
    go (TTuple ts) = goMany ts
    go _ = return Delay

    goMany ts = return $ Split [PredHasDefaultValue (p ++ [Left i]) t l | (i, t) <- zip [0..] ts]

    goStruct x ts = do
      msenv <- tcLookupStruct (varName x)
      case msenv of
        Nothing -> return Delay
        Just StructEnv{..} -> do
          let TForAll vs _ _ = _structType
          let sub = fromListUM $ zip vs ts
          let mkF fi = (_fieldName fi, subType sub (_fieldType fi))
          let fs = map mkF $ Map.elems _structFields
          let preds = [PredHasDefaultValue (p ++ [Right n]) t l | (n, t) <- fs]
          return $ Split preds

-- TODO: This looks bit iffy how we translate to equalities.
-- Verify that we are dealing correctly with levels here.
tryElimDomainLe :: DomainType Var -> DomainType Var -> Location -> Level -> ElimResult
tryElimDomainLe d1 d2 l level = go (simpType d1) (simpType d2)
  where
    go (TDomain d) (TDomain d') | d <= d' = mkRemove
    go (TDomain TVPublic) _ = mkRemove -- @public <= _
    go _ (TDomain TVProver) = mkRemove -- _ <= @prover
    go (TVar x _ _) (TVar y _ _) | x == y = mkRemove -- @x <= @x
    go (TVar x _ _) (TDomain tvd) -- @d <= @public --> @d = @public
      | tvd == TVPublic && isMetaTyVar x && not (varIsUntouchable x level) =
        Split [PredEq d1 mkPublicDomain l]
    go (TDomain tvd) (TVar x _ _) -- @prover <= @d --> @prover = @d
      | tvd == TVProver && isMetaTyVar x && not (varIsUntouchable x level) =
        Split [PredEq mkProverDomain d2 l]
    go _ _ = Delay

tryElimPossibleInput :: GetInputFn -> UnqualifiedType Var ->
  StageType Var -> DomainType Var -> Location -> ElimResult
tryElimPossibleInput fn ty stage dom l =
  go ty stage dom
  where
    go TUInt{} s d = goScalar s d
    go TBool{} s d = goScalar s d
    go (TList qualElTy) (TStage TVPre) dom | goodDom dom =
      case qualElTy of
        TQualify elemTy elemStage elemDom ->
          goComponent elemTy elemStage elemDom
        _ -> Delay
    go (TList _) s d
      | isVar s = unifyStagePre
      | isVar d = unifyDom
      
    go (TTuple qualifiedShapes) (TStage TVPre) (TDomain TVPublic) =
      let shapeConstraints = flip map qualifiedShapes $ \case
            TQualify elemTy elemStage elemDom ->
              goComponent elemTy elemStage elemDom
            _ -> Delay
          merge _ Delay = Delay
          merge Delay _ = Delay
          merge (Split constr) (Split acc) = Split (constr ++ acc)
          mergedConstraints = foldr merge (Split []) shapeConstraints
      in
        mergedConstraints

    go (TTuple _) s d
      | isVar s = unifyStagePre
      | isVar d = addConstr $ PredEq dom mkPublicDomain l
    go _ _ _ = Delay

    goScalar s d
      | goodStage s && goodDom d = mkRemove
      | isVar s = addConstr $ PredEq stage mkPre l
      | isVar d = addConstr $ PredEq dom mkDom l
      | otherwise = Delay

    goComponent elemTy elemStage elemDom =
      Split [PredPossibleInput fn elemTy elemStage elemDom l]

    goodStage (TStage TVPre) = True
    goodStage _ = False

    goodDom dom = case (fn, dom) of
      (GetWitness, TDomain TVProver)    -> True
      (GetInstance, TDomain TVVerifier) -> True
      (GetPublic, TDomain TVPublic)     -> True
      _                                 -> False

    mkDom = case fn of
      GetInstance -> mkVerifierDomain
      GetPublic   -> mkPublicDomain
      GetWitness  -> mkProverDomain

    isVar TVar{} = True
    isVar _ = False

    addConstr pred = Split [pred, PredPossibleInput fn ty stage dom l]

    unifyStagePre = addConstr $ PredEq stage mkPre l

    unifyDom = addConstr $ PredEq dom mkDom l

data ElimWireResult
  -- qualified type is scalar
  = ElimWireScalarConstraints [TypePred Var]
  -- qualified type is tuple or struct
  | ElimWireCompoundConstraints [TypePred Var]
  -- qualifid type is list
  | ElimWireListConstraints [TypePred Var]
  | ElimWireDelay

addConstraint :: TypePred Var -> ElimWireResult -> TcM ElimWireResult
addConstraint _ ElimWireDelay = return ElimWireDelay
addConstraint c (ElimWireCompoundConstraints cs) =
  return $ ElimWireCompoundConstraints (c : cs)
addConstraint c (ElimWireListConstraints cs) =
  return $ ElimWireListConstraints (c : cs)
addConstraint c (ElimWireScalarConstraints cs) =
  return $ ElimWireScalarConstraints (c : cs)

withTupleShapeComponents
  :: Type Var
  -> Int
  -> Location
  -> ([Type Var] -> TcM ElimWireResult)
  -> TcM ElimWireResult
withTupleShapeComponents ty nComponents loc cont =
  case ty of
    TVar {} -> do
      componentVars <- replicateM nComponents tcFreshQualifiedTy'
      let tupleType = TApp (TCon (ConTuple nComponents) loc) componentVars loc
      let constraint = PredEq ty tupleType loc
      addConstraint constraint =<< cont componentVars

    TTuple components -> cont components

    _ -> return ElimWireDelay

withShapeListElem
  :: Type Var
  -> Location
  -> (Type Var -> TcM ElimWireResult)
  -> TcM ElimWireResult
withShapeListElem shapeTy loc cont =
  case shapeTy of
    TVar {} -> do
      elemVar <- tcFreshQualifiedTy'
      let listType = TApp (TCon ConList loc) [elemVar] loc
      let constraint = PredEq shapeTy listType loc
      addConstraint constraint =<< cont elemVar

    TList elem -> cont elem

    _ -> return ElimWireDelay

wireUnifyTupleVar :: Type Var -> [Type Var] -> Type Var -> Location ->
  Bool -> TcM ElimWireResult
wireUnifyTupleVar shapeType tupleComponentTypes typeVar loc varIsFrom = do
  let n = length tupleComponentTypes
  withTupleShapeComponents shapeType n loc $ \shapeComponents -> do
    componentVars <- replicateM n tcFreshQualifiedTy'
    let componentConstraints
          | varIsFrom =
            zipWith3 wireConstr
            shapeComponents componentVars tupleComponentTypes
          | otherwise =
            zipWith3 wireConstr
            shapeComponents tupleComponentTypes componentVars
    let varTuple = TApp (TCon (ConTuple n) loc) componentVars loc
    let structureConstraint = PredEq typeVar varTuple loc
    return $ ElimWireCompoundConstraints
      (structureConstraint : componentConstraints)
  where
    wireConstr shape from to = PredWireExpr shape from to loc

tryElimWireUnqualified
  :: UnqualifiedType Var
  -> UnqualifiedType Var
  -> UnqualifiedType Var
  -> Location
  -> TcM ElimWireResult
tryElimWireUnqualified shapeTy fromTy toTy loc = tcSetLoc loc $
  case (fromTy, toTy) of
    -- tuples
    (TTuple fromTys, TTuple toTys) -> do
      withTupleShapeComponents shapeTy (length fromTys) loc $
        \shapeComponents -> compound $ zipWith3
          (\shape from to -> PredWireExpr shape from to loc)
          shapeComponents fromTys toTys

    (TTuple componentTys, TVar {}) ->
      wireUnifyTupleVar shapeTy componentTys toTy loc False

    (TVar {}, TTuple componentTys) ->
      wireUnifyTupleVar shapeTy componentTys fromTy loc True

    -- lists
    (TList fromElem, TList toElem) ->
      withShapeListElem shapeTy loc $ \shapeElem ->
        list [PredWireExpr shapeElem fromElem toElem loc]

    (TList fromElem, TVar {}) ->
      withShapeListElem shapeTy loc $ \shapeElem -> do
        toElem <- tcFreshQualifiedTy'
        let toList = TApp (TCon ConList loc) [toElem] loc
        list [ PredEq toTy toList loc
             , PredWireExpr shapeElem fromElem toElem loc
             ]

    (TVar {}, TList toElem) ->
      withShapeListElem shapeTy loc $ \shapeElem -> do
        fromElem <- tcFreshQualifiedTy'
        let fromList = TApp (TCon ConList loc) [fromElem] loc
        list [ PredEq fromTy fromList loc
             , PredWireExpr shapeElem fromElem toElem loc
             ]

    -- scalars
    (f, t) | isScalar f || isScalar t -> let
         rings = catMaybes [scalarRing f, scalarRing t]
       in
       scalar $
             [ PredPostRing (head rings) loc
             , PredEq shapeTy (mkCon ConUnit) loc
             , PredEq fromTy toTy loc
             ]

    _ -> return ElimWireDelay

  where
    scalar = return . ElimWireScalarConstraints
    compound = return . ElimWireCompoundConstraints
    list = return . ElimWireListConstraints

    scalarRing (TInt r) = Just r
    scalarRing (TBin r) = Just r
    scalarRing _        = Nothing
    
    isScalar = isJust . scalarRing

tryElimWire :: Type Var -> Type Var -> Type Var -> Location -> TcM ElimResult
tryElimWire shape from to loc =
  case (shape, from, to) of
    (TQualify shapeTy _ shapeDom,
     TQualify fromTy fromStage fromDom,
     TQualify toTy toStage toDom) -> do
      elim <- tryElimWireUnqualified shapeTy fromTy toTy loc
      case elim of
        ElimWireDelay -> return Delay

        ElimWireScalarConstraints cs ->
          return $ Split $
            PredEq fromStage mkPre loc :
            PredEq toStage mkPost loc :
            PredEq fromDom toDom loc :
            cs

        ElimWireCompoundConstraints cs ->
          return $ Split $
            PredEq fromStage toStage loc :
            PredEq fromDom toDom loc :
            cs

        ElimWireListConstraints cs ->
          return $ Split $
            PredEq fromStage toStage loc :
            PredEq toDom shapeDom loc :
            cs

    _ -> return Delay

-- Substitute variable x with type t if x does not occur in t.
-- Assumes that occurs check passes and throws an error if that's not the case.
-- This function applies the substitution to existing substitutions and then
-- inserts it into the substitution map and removes the meta variable x from the
-- set of unsolved variables.
addSub :: MetaTyVar -> Type Var -> Level -> TcM ElimResult
addSub x t level
  | not (isMetaTyVar x) = tcFatal "ICE: Expecting meta variable."
  | varIsUntouchable x level = tcFatal "ICE: Unexcpected untouchable meta variable."
  | x `occursIn` t = tcThrowErr "Occur check failed. Constructing infinite type."
  | otherwise = do
    tcAddSub x t
    tcRemoveUnsolved x
    return mkRemove

-- TODO: can be optimized to eliminate the need for constructing list
occursIn :: Var -> Type Var -> Bool
occursIn x t = x `elem` typeGetVars t

-- At this stage in compiler all type variable applications are injective.
-- Type synonyms can be noninjective but they have been eliminated at this point.
-- Structures are always clearly injective.
-- If we add interfaces with (noninjective) associated types we would have to
-- handle applications f[e1,...,en] much more carefully.
typeIsInjective :: Type TyVar -> Bool
typeIsInjective (TCon c _) = typeConIsInjective c
typeIsInjective TVar{} = True
typeIsInjective (TApp t _ _) = typeIsInjective t
typeIsInjective (TSelf _) = True

castAnyKind :: Type TyVar -> DomainType TyVar -> Type TyVar
castAnyKind t = ($ t) $ case typeKind t of
  KindStar -> TCast
  KindUnqualified -> TCastUnqual
  KindStage -> TCastStage
  KindDomain -> TCastDomain
  _ -> const

simpType :: Type TyVar -> Type TyVar
simpType = transform go
  where
  go (TQualify (TGetUnqual t1) (TGetStage t2) (TGetDomain t3))
    | t1 == t2, t2 == t3 = t1
  go (TGetUnqual (TQualify u _ _)) = u
  go (TGetStage (TQualify _ s _)) = s
  go (TGetDomain (TQualify _ _ d)) = d
  go (TCastUnqual (TGetUnqual q) d) = go (TGetUnqual (go (TCast q d)))
  go (TCastStage (TGetStage q) d) = go (TGetStage (go (TCast q d)))
  go (TCastDomain (TGetDomain q) d) = go (TGetDomain (go (TCast q d)))
  go (TCast (TQualify u s d1) d) = mkQualified (go (TCastUnqual u d)) (go (TCastStage s d)) (go (TCastDomain d1 d))
  go (TCastUnqual t@TUnit _) = t
  go (TCastUnqual t@TString _) = t
  go (TCastUnqual (TFun q1 q2) d) = TApp (mkCon ConFun) [go q1, go (TCast q2 d)] NoLocation
  go (TCastUnqual (TApp t ts l) d) = TApp t (map (go . (castAnyKind `flip` d)) ts) l
  go (TCastStage s@(TStage TVPre) _) = s
  go (TCastStage s (TDomain TVPublic)) = s
  go (TCastStage _ (TDomain TVVerifier)) = mkPre
  go (TCastStage _ (TDomain TVProver)) = mkPre
  go (TCastStage (TCastStage s d1) d2) | d1 == d2 = go (TCastStage s d1)
  go (TCastDomain (TDomain TVPublic) d) = d
  go (TCastDomain d (TDomain TVPublic)) = d
  go (TCastDomain d@(TDomain TVProver) _) = d
  go (TCastDomain _ d@(TDomain TVProver)) = d
  go (TCastDomain d@(TDomain TVVerifier) (TDomain TVVerifier)) = d
  go (TCastDomain d1 d2) | d1 == d2 = d1
  go t = t

mkGetUnqual :: QualifiedType a -> Location -> UnqualifiedType a
mkGetUnqual t l = TApp (TCon ConGetUnqual l) [t] l

mkGetStage :: QualifiedType a -> Location -> StageType a
mkGetStage t l = TApp (TCon ConGetStage l) [t] l

mkGetDomain :: QualifiedType a -> Location -> DomainType a
mkGetDomain t l = TApp (TCon ConGetDomain l) [t] l

splitQualEqVar :: QualifiedType TyVar -> QualifiedType TyVar -> ElimResult
splitQualEqVar (TQualify t1 s1 d1) v@(TVar _ _ l) =
  Split [PredEq t1 (mkGetUnqual v l) l, PredEq s1 (mkGetStage v l) l, PredEq d1 (mkGetDomain v l) l]
splitQualEqVar v@(TVar _ _ l) (TQualify t1 s1 d1) =
  Split [PredEq (mkGetUnqual v l) t1 l, PredEq (mkGetStage v l) s1 l, PredEq (mkGetDomain v l) d1 l]
splitQualEqVar _ _ = Delay

tcCheckConstr :: TypePreds -> TcM ()
tcCheckConstr cs = do
  forM_ cs $ \c -> tcSetLoc (location c) $ do
    tcAddErr $ "Unsolved constraints:" <+> pretty c

tryElimEq :: Type Var -> Type Var -> Location -> Level -> TcM ElimResult
tryElimEq ty1 ty2 l level = tcSetLoc l $ go (simpType ty1) (simpType ty2) l
  where
    go (TVar x _ _) (TVar y _ _) _ | x == y = return mkRemove
    go (TVar x _ _) _  _ | canUnifyVar x = addSub x ty2 level
    go _ (TVar x _ _) _ | canUnifyVar x = addSub x ty1 level
    go (TCon c _) (TCon c' _) _ | c == c' = return mkRemove
    go q@TQualify{} v@(TVar y _ _) _ | isTyVar y = return $ splitQualEqVar q v
    go v@(TVar x _ _) q@TQualify{} _ | isTyVar x = return $ splitQualEqVar v q
    go t1@TCastUnqual{} t2 l = handleCastUnqual l t1 t2
    go t2 t1@TCastUnqual{} l = handleCastUnqual l t1 t2
    go (TApp x xs _) (TApp y ys _) l
      | length xs /= length ys = throwUnexpectedTypesError "Mismatching number of type constructor arguments."
      | typeIsInjective x && typeIsInjective y =
        return $ Split $ zipWith (\t1 t2 -> PredEq t1 t2 l) (x : xs) (y : ys)
    go _ _ _ = return Delay

    handleCastUnqual l (TCastUnqual t1 d) = \case
      t2@TUInt{} -> return $ Split [PredEq t1 t2 l]
      t2@TBool{} -> return $ Split [PredEq t1 t2 l]
      t2@TString -> return $ Split [PredEq t1 t2 l]
      t2@TUnit -> return $ Split [PredEq t1 t2 l]
      t2@TStore{} -> return $ Split [PredEq t1 t2 l] -- store keys and values are currently scalar and thus do not contain inner domains or stages
      TList q -> do
        q' <- tcFreshQualifiedTy'
        return $ Split [PredEq t1 (TApp (mkCon ConList) [q'] l) l, PredEq q (TCast q' d) l]
      TArr q -> do
        q' <- tcFreshQualifiedTy'
        return $ Split [PredEq t1 (TApp (mkCon ConArr) [q'] l) l, PredEq q (TCast q' d) l]
      TTuple qs -> do
        qs' <- mapM (const tcFreshQualifiedTy') qs
        return $ Split $ PredEq t1 (TApp (mkCon (ConTuple (length qs))) qs' l) l :
                         zipWith (\ q q' -> PredEq q (TCast q' d) l) qs qs'
      TFun q1 q2 -> do
        q2' <- tcFreshQualifiedTy'
        return $ Split [PredEq t1 (TApp (mkCon ConFun) [q1, q2'] l) l, PredEq q2 (TCast q2' d) l]
      _ -> return Delay
    handleCastUnqual _ _ = const $ return Delay

    canUnifyVar x = isMetaTyVar x && not (varIsUntouchable x level)

    throwUnexpectedTypesError msg = do
      let pprintQ = doubleQuotes . pretty
      let ty1Str = pprintQ ty1
      let ty2Str = pprintQ ty2
      tcThrowErr $ msg <+> "Expected" <+> ty1Str <> ", got" <+> ty2Str <> "."
