{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Typing.KindChecker (
  tcCheckTypeKind,
  tcCheckTypeKind',
  tcInferTypeKind,
  tcNoStageToMetaVar,
  tcType,
  tcTypeNoReplaceMissingStages,
  tcTypePred,
  tcConstraint
) where

import Control.Monad
import Control.Monad.Reader
import Control.Lens

import Parser.Syntax
import Basic.Name
import Typing.TcM
import Basic.Var
import Support.Pretty
import Basic.Location
import Typing.Kind
import Support.UniqMap

tcCheckTypeKind :: Kind -> Type Name -> TcM (Kind, Type Var)
tcCheckTypeKind resKind (TVar name k1 l) = tcSetLoc l $ do
  mres <- tcLookupType name
  case mres of
    Just (k2, TForAll{..}) -> do
      unless (null _typeSchemeQuantifiers) $
        tcThrowErr "Missing type arguments."
      unless (null _typeSchemePredicates) $
        tcThrowErr "Type synonym constraints not yet supported."
      k <- tcUnifyKinds k1 k2
      tcKindConvTo k resKind
      -- Strip locations of expanded type synonyms
      let resType = transform stripLocation _typeSchemeType `setLocation` l
      return $ implicitlyQualify resKind k resType
    Nothing -> do
      var <- tcFindTyVar name
      let k2 = tyVarKind var
      k <- tcUnifyKinds k1 k2
      return $ implicitlyQualify resKind k (TVar var k l)
tcCheckTypeKind resKind (TCon con l) = tcSetLoc l $ do
  let k = typeConKind con
  tcKindConvTo k resKind
  return $ implicitlyQualify resKind k (TCon con l)
tcCheckTypeKind resKind t@TApp{} = do
  (k, t') <- tcInferTypeKind t
  tcKindConvTo k resKind
  return $ implicitlyQualify resKind k t'
tcCheckTypeKind resKind (TSelf l) = do
  let k = KindStar
  tcKindConvTo k resKind
  return $ implicitlyQualify resKind k (TSelf l)

tcInferTypeKind :: Type Name -> TcM (Kind, Type Var)
tcInferTypeKind t@(TVar x _ l) = tcSetLoc l $ do
    my <- tcLookupTyVar x -- case type has been introduced via forall quantifier
    case my of
      Nothing -> tcInferTypeAppKind t [] -- otherwise handle the type synonym case
      Just y -> let k = tyVarKind y in return (k, TVar y k l)
tcInferTypeKind (TCon con l) = return (typeConKind con, TCon con l)
tcInferTypeKind (TApp t ts l) = tcSetLoc l $ tcInferTypeAppKind t ts
tcInferTypeKind (TSelf l) = return (KindStar, TSelf l)

tcInferTypeAppKind :: Type Name -> [Type Name] -> TcM (Kind, Type Var)
tcInferTypeAppKind t ts = case t of
  TVar name k1 l -> do
    mSyn <- tcLookupType name
    let m = length ts
    case mSyn of
      Just (k2, TForAll vs _ resTy) -> do
        -- Type synonyms.
        k <- tcUnifyKinds k1 k2
        let n = length vs
        unless (n == m) $
          tcThrowErr $
            "Unexpected number of type arguments" <+>
            "Expected" <+> pretty n <+> "type arguments but got" <+> pretty m <> "."
        (argKs, resK) <- splitKind n k
        tcAddSynonymOccur name l
        ts' <- zipWithM tcCheckTypeKind' argKs ts
        let subst = fromListUM (zip vs ts')
        let resTy' = subType subst resTy
        return (resK, resTy')
      Nothing -> do
        -- Structs.
        var <- tcFindTyVar name
        let k2 = tyVarKind var
        k <- tcUnifyKinds k1 k2
        (argKs, resK) <- splitKind m k
        ts' <- zipWithM tcCheckTypeKind' argKs ts
        l <- tcGetLoc
        let resTy = TApp (TVar var k (location var)) ts' l
        return $ implicitlyQualify resK k resTy
  TCon con l -> do
    let kindFun = typeConKind con
    (kindArgs, k) <- splitKind (length ts) kindFun
    ts' <- zipWithM tcCheckTypeKind' kindArgs ts
    l' <- tcGetLoc
    return (k, TApp (TCon con l) ts' l')
  _ -> tcSetLoc (location t) $
    tcThrowErr "Unsupported type application."

splitKind :: Int -> Kind -> TcM ([Kind], Kind)
splitKind n _ | n < 0 = tcICE "Negative number of kind arguments."
splitKind 0 k = return ([], k)
splitKind n (KindFun kArg kRes) = do
  (ks, k) <- splitKind (n - 1) kRes
  return (kArg : ks, k)
splitKind _ _ = tcThrowErr "Too many type arguments."

throwKindMismatch :: Kind -> Kind -> TcM a
throwKindMismatch k1 k2 = tcThrowErr $
  "Kind mismatch." <+>
  "Expected kind" <+> pretty k2 <+> "got kind" <+> pretty k1 <> "."

tcUnifyKinds :: Kind -> Kind -> TcM Kind
tcUnifyKinds k1 k2 = case unifyKinds k1 k2 of
  Nothing -> throwKindMismatch k1 k2
  Just k -> return k

tcKindConvTo :: Kind -> Kind -> TcM ()
tcKindConvTo k1 k2
  | kindConvTo k1 k2 = return ()
  | otherwise = throwKindMismatch k1 k2

implicitlyQualify :: Kind -> Kind -> Type Var -> (Kind, Type Var)
implicitlyQualify resKind actualKind t = (resKind, t')
  where
    t' = case (resKind, actualKind) of
      (KindStar, KindUnqualified) -> let
          l = location t
          s = mkNoStage `setLocation` l
          d = mkPublicDomain `setLocation` l
        in mkQualifiedL t s d l
      _ -> t

data NoStageHandling
  = ReplaceNoStage
  | KeepNoStage

tcTypeHelper :: Kind -> Type Name -> NoStageHandling -> TcM (Type Var)
tcTypeHelper k ty noStageHandling = flip tcWrapLoc' ty $ \ty -> do
  ty' <- tcCheckTypeKind' k ty
  ty'' <- tcAddImplicitPreAndDom ty'
  ty''' <- case noStageHandling of
      ReplaceNoStage -> tcNoStageToMetaVar ty''
      KeepNoStage -> return ty''
  tcTypeGenerateImplicitConstraints ty'''
  return ty'''

tcTypeNoReplaceMissingStages :: Kind -> Type Name -> TcM (Type Var)
tcTypeNoReplaceMissingStages k ty = tcTypeHelper k ty KeepNoStage

tcType :: Kind -> Type Name -> TcM (Type Var)
tcType k ty = tcTypeHelper k ty ReplaceNoStage

tcCheckTypeKind' :: Kind -> Type Name -> TcM (Type Var)
tcCheckTypeKind' k t = snd <$> tcCheckTypeKind k t

tcAddImplicitPreAndDom :: QualifiedType TyVar -> TcM (QualifiedType TyVar)
tcAddImplicitPreAndDom = go
  where
    go c@TCon{} = return c
    go x@TVar{} = return x
    go t@(TQualify u s d) = do
      isStruct <- tcIsStruct u
      u' <- go u
      let s' = newStage isStruct u' s
      let d' = newDomain isStruct u' d
      let l = location t
      return $ mkQualifiedL u' s' d' l
    go (TApp  t ts l) = TApp <$> go t <*> mapM go ts <*> pure l
    go (TSelf l) = return $ TSelf l

    newStage isStruct u s
      | TStage TVNoStage <- s, mustBePre isStruct u = mkPre
      | otherwise = s

    newDomain isStruct u d
      | TDomain TVNoDomain <- d, defaultsToPublic isStruct u = mkPublicDomain
      | otherwise = d

    mustBePre isStruct = \case
      TString{} -> True
      TFun{} -> True
      TList{} -> True
      TArr{} -> True
      TTuple{} -> True
      _ -> isStruct

    defaultsToPublic isStruct = \case
      TBool{} -> True
      TString -> True
      TUnit -> True
      TUInt{} -> True
      TFun{}  -> True
      TList{} -> True
      TArr{} -> True
      TTuple{} -> True
      TStore{} -> True
      _ -> isStruct

-- Generate implicit constraints from type.
-- For example "(t1 -> t2) $s @d" generates constraint "$s = $pre /\ @d = @public".
-- Among other things this catches errors such as "string $post @prover" (because
-- strings can only exist in %pre stage).
tcTypeGenerateImplicitConstraints :: QualifiedType Var -> TcM ()
tcTypeGenerateImplicitConstraints ty = runReaderT (go ty) noCtx
  where
    go t = case t of
      TString -> emitIsPre
      TFun{} -> emitIsPre >> emitIsPub >> goChildren goNoCtx t
      TList{} -> emitIsPre >> goChildren goNoCtx t
      TArr{} -> emitIsPre >> goChildren goNoCtx t
      TTuple{} -> emitIsPre >> goChildren goNoCtx t
      TQualify t stage dom -> setCtx stage dom t
      _ -> goChildren goNoCtx t

    noCtx = (Nothing, Nothing)

    setCtx stage dom t = local (const (Just stage, Just dom)) (go t)

    goNoCtx t = local (const noCtx) (go t)

    goChildren f t = mapM_ f (children t)

    -- context must have pre stage
    emitIsPre = do
      ctx <- asks fst
      case ctx of
        Nothing -> return ()
        Just stageCtx -> case stageCtx of
          TStage TVNoStage -> return ()
          _ -> lift (tcUnifyTypes stageCtx mkPre)

    emitIsPub = do
      ctx <- asks snd
      case ctx of
        Nothing -> return ()
        Just domCtx -> lift (tcUnifyTypes domCtx mkPublicDomain)

tcNoStageToMetaVar :: Type Var -> TcM (Type Var)
tcNoStageToMetaVar = transformM replaceNoStage
  where
    replaceNoStage (TCon ConNoStage l) = do
      metaVar <- tcFreshMetaTyVar KindStage
      return $ TVar (setLocation metaVar l) KindStage l
    replaceNoStage t = return t

tcConstraint :: [TypePred Name] -> TcM [TypePred Var]
tcConstraint = traverse tcTypePred

tcTypePred :: TypePred Name -> TcM (TypePred Var)
tcTypePred tp@(TypePred _ _ l) = tcSetLoc l $ case tp of
  PredSub d1 d2 _ -> PredSub <$> tcType KindDomain d1 <*> tcType KindDomain d2 <*> pure l
  PredPre t _ -> PredPre <$> tcType KindStage t <*> pure l
  PredPost t _ -> PredPost <$> tcType KindStage t <*> pure l
  PredArray t _ -> PredArray <$> tcType (KindStar `KindFun` KindUnqualified) t <*> pure l
  PredSized t _ -> PredSized <$> tcType KindStar t <*> pure l
  PredPostRing t _ -> PredPostRing <$> tcType KindRing t <*> pure l
  PredPostConvertible t1 t2 _ -> PredPostConvertible <$> tcType KindRing t1 <*> tcType KindRing t2 <*> pure l
  PredChallenge t _ -> PredChallenge <$> tcType KindRing t <*> pure l
  PredExtendedArithmetic _ -> PredExtendedArithmetic <$> pure l
  PredPermutationCheck _ -> PredPermutationCheck <$> pure l
  PredVectors _ -> PredVectors <$> pure l
  PredVectorization _ -> PredVectorization <$> pure l
  PredObliviousChoice _ -> PredObliviousChoice <$> pure l
  _ -> tcICE "Unsupported predicate."
