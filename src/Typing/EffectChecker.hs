{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
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

module Typing.EffectChecker (ecModules, ecExpr) where

import Basic.Location
import Basic.Message
import Basic.Name (mkName, nameBuiltinInfo, BuiltinInfo(..), mainFName, nameOccName)
import Basic.Var
import Parser.Effect hiding (Effect', TypeWithEffect')
import qualified Parser.Effect
import Parser.Syntax
import Support.Bag
import Support.Pretty
import Support.UniqMap
import Support.Unique
import Typing.StructEnv
import Typing.Typing (TypedProgram(..), TypedTopExtern(..), TypedTopFunction(..))

import Control.Arrow hiding ((<+>))
import Control.Exception
import Control.Lens hiding (List)
import Control.Monad.Except
import Control.Monad.RWS
import Data.Either (partitionEithers)
import Data.Foldable
import Data.List
import Data.Maybe
import GHC.Exception
import GHC.Stack (HasCallStack, callStack)
import System.IO (hPutStrLn, stderr)

import qualified Data.Text as T

-- A hack to allow using Text instead of TyVar during parsing
-- but still allow the derived Functor and Foldable instances to work correctly with TyVar,
-- otherwise there was an infinite loop when effect checking Std.zksc.
type Effect' = Parser.Effect.Effect' TyVar
type TypeWithEffect' = Parser.Effect.TypeWithEffect' TyVar

{-
 - Limitations:
 - 1. Higher order functions defined inside structs always have public effect
 - 2. Inferred type of function arguments are always simply polymorphic. Think map function.
 -    For example `(any -> any ! <@public>) -> any ! <@public>` will never be inferred.
 -}

-------------------
-- Effect system --
-------------------

effectHasNoMetaVars :: Effect' a -> Bool
effectHasNoMetaVars = null . _effectMetaVars

splitFunTwe :: HasCallStack => TypeWithEffect -> Int -> ([TypeWithEffect], TypeWithEffect, Effect, [EffConstraint])
splitFunTwe t 0 = ([], t, mempty, [])
splitFunTwe _ n | n < 0 = error "Negative input"
splitFunTwe (TweFun t1 t2 e cs) n = let ~(ts', t', e', cs') = splitFunTwe t2 (n - 1) in (t1 : ts', t', e <> e', cs ++ cs')
splitFunTwe _ _ = error "Too few function arguments."

tweApplySubst :: Var -> Effect -> TypeWithEffect -> TypeWithEffect
tweApplySubst x e = go
  where
    go TweAny = TweAny
    go (TweTuple ts) = TweTuple (map go ts)
    go (TweFun t1 t2 eff cs) = TweFun (go t1) (go t2) (effectApplySubst x e eff) cs

effectApplySubst :: Var -> Effect -> Effect -> Effect
effectApplySubst x e' e@(Effect xs ts)
  | x `elem` xs = e' <> Effect (delete x xs) ts
  | otherwise = e

effCApplySubst :: EffectVar -> Effect -> EffConstraint -> EffConstraint
effCApplySubst x e (EffUnify t1 t2 l) = EffUnify (tweApplySubst x e t1) (tweApplySubst x e t2) l
effCApplySubst x e (EffEq e1 e2 l) = EffEq (effectApplySubst x e e1) (effectApplySubst x e e2) l
effCApplySubst x e (EffLe e1 e2 l) = EffLe (effectApplySubst x e e1) (effectApplySubst x e e2) l

tweApplySubsts :: UniqMap Effect -> TypeWithEffect -> TypeWithEffect
tweApplySubsts esub = go
  where
    go TweAny = TweAny
    go (TweTuple ts) = TweTuple (map go ts)
    go (TweFun t1 t2 eff cs) = TweFun (go t1) (go t2) (effectApplySubsts esub eff) cs

effectApplySubsts :: UniqMap Effect -> Effect -> Effect
effectApplySubsts esub (Effect xs ts) = mconcat (Effect ys ts : es)
  where
    (ys, es) = partitionEithers $ map lookup xs
    lookup x = case lookupUM x esub of
      Nothing -> Left x
      Just eff -> Right $ effectApplySubsts esub eff

effCApplySubsts :: UniqMap Effect -> EffConstraint -> EffConstraint
effCApplySubsts um = go
  where
    goE = effectApplySubsts um
    goT = tweApplySubsts um
    go = \case
      EffUnify t1 t2 l -> EffUnify (goT t1) (goT t2) l
      EffEq e1 e2 l -> EffEq (goE e1) (goE e2) l
      EffLe e1 e2 l -> EffLe (goE e1) (goE e2) l

mkFunTwe :: HasCallStack => [TypeWithEffect] -> TypeWithEffect -> Effect -> TypeWithEffect
mkFunTwe [] _ _ = error "ICE: Missing argument."
mkFunTwe [t1] t2 eff = TweFun t1 t2 eff []
mkFunTwe (t1 : ts) t2 effs = TweFun t1 (mkFunTwe ts t2 effs) mempty []

-- Does not check if stage is $post
isFieldConv
  :: Type a -> Type a -> Bool
isFieldConv (TQualify u _ _) t
  = let
      isFieldConv u                (TQualify u' _ _)
        = isFieldConv u u'
      isFieldConv (TUInt (TNat m)) (TUInt (TNat m'))
        = m /= m'
      isFieldConv (TBool (TNat m)) (TBool (TNat m'))
        = m /= m'
      isFieldConv _                _
        = False
    in
    isFieldConv u t
isFieldConv _                              _
  = False

typeSchemeApply :: TypeScheme TyVar -> [Type TyVar] -> UniqMap (Type TyVar)
typeSchemeApply (TForAll xs _ _) ts = assert (length xs == length ts) $ fromListUM (zip xs ts)

type ErrMsg = Doc ()


---------------------------------
-- Effect checking monad (EcM) --
---------------------------------

data EcOut = EcOut
  { _effects  :: Effect
  , _messages :: Bag Message
  , _constraints :: [EffConstraint]
  , _unsolvedEffectVars :: UniqMap EffectVar
  , _breakContexts :: [DomainType TyVar]
  }

data EcCtx = EcCtx
  { _loc :: Location
  , _verbose :: Bool
  , _debugPrintEffectTypes :: Bool
  , _structsEnv :: StructsEnv
  , _env :: UniqMap ([EffectVar], TypeWithEffect)
  , _resultType :: Maybe (Type TyVar)
  }

data EcState = EcState
  { _uniq :: Unique
  , _effectVarNum :: Int
  }

makeLenses ''EcOut
makeLenses ''EcCtx
makeLenses ''EcState

-- Fully censors a field in writer.
clearing :: (MonadWriter w m, Monoid v) => Setter w w u v -> m a -> m a
clearing s = censoring s (const mempty)

instance Semigroup EcOut where
  EcOut e1 b1 c1 ev1 bc1 <> EcOut e2 b2 c2 ev2 bc2 = EcOut (e1 <> e2) (b1 <> b2) (c1 <> c2) (ev1 <> ev2) (bc1 <> bc2)

instance Monoid EcOut where
  mempty = EcOut mempty mempty mempty mempty mempty

data EcException = EcException ErrMsg Location

type EcM a = RWST EcCtx EcOut EcState (ExceptT EcException IO) a

runEcM :: EcM a -> Bool -> Bool -> Unique -> StructsEnv -> IO (Either Messages (a, Unique))
runEcM act v verbosePrintEffectTypes u senv = do
  let initCtx = EcCtx 
                { _verbose = v
                , _debugPrintEffectTypes = verbosePrintEffectTypes
                , _loc = NoLocation
                , _env = emptyUM
                , _structsEnv = senv
                , _resultType = Nothing 
                }
  let initState = EcState { _uniq = u, _effectVarNum = 0 }
  res <- runExceptT (runRWST act initCtx initState)
  return $ case res of
    Left ex -> Left $ ecExceptionToMessages ex
    Right (x, EcState{..}, EcOut{..}) -> if nullBag _messages
        then Right (x, _uniq)
        else Left _messages

ecExceptionToMessages :: EcException -> Messages
ecExceptionToMessages (EcException doc loc) = 
   singletonBag $
   (if render doc == forbiddenOperErrMsg then errMsg else warnMsg) doc [loc]

forbiddenOperErrMsg :: String
forbiddenOperErrMsg = "Direct or indirect invokation of a forbidden operation"

-- Catch exception if one is thrown and record it as error message.
ecIgnoreEx :: EcM a -> EcM (Maybe a)
ecIgnoreEx act =
  catchError (Just <$> act) $ \ ex -> do
    messages `scribe` ecExceptionToMessages ex
    return Nothing

ecIce :: HasCallStack => ErrMsg -> EcM a
ecIce msg = do
  let stack = hcat $ map pretty $ prettyCallStackLines callStack
  ecThrow ("ICE:" <+> msg $$ indent 2 stack)

ecThrow :: ErrMsg -> EcM a
ecThrow msg = do
  l <- asks _loc
  throwError (EcException msg l)

ecFail :: Messages -> EcM a
ecFail msgs = lift . lift $ throwIO msgs

verbosePrint :: Doc ann -> EcM ()
verbosePrint doc = do
  verbose <- asks _verbose
  when verbose $
    liftIO $ hPutStrLn stderr $ render doc


---------------------
-- Effect checking --
---------------------

ecUnifyTwe :: TypeWithEffect -> TypeWithEffect -> EcM ()
ecUnifyTwe TweAny _ = return ()
ecUnifyTwe _ TweAny = return ()
ecUnifyTwe (TweTuple ts) (TweTuple ts') | length ts == length ts' = zipWithM_ ecUnifyTwe ts ts'
ecUnifyTwe (TweFun t1 t2 e cs) (TweFun t1' t2' e' cs') = do
  l <- asks _loc
  ecUnifyTwe t1 t1'
  ecUnifyTwe t2 t2'
  constraints `scribe` [EffEq e e' l]
  when (not (null cs) || not (null cs')) $ ecThrow "Effect constraints not yet supported for higher-order functions"
ecUnifyTwe t1 t2 = do
  l <- asks _loc
  constraints `scribe` [EffUnify t1 t2 l]

ecLit :: Constant -> EcM ()
ecLit lit = do
  Just t <- asks _resultType
  (_, s, _) <- ecSplitQualified t
  case lit of
    ConstBool _ -> effects `scribe` mkEffect s
    ConstInt _ -> effects `scribe` mkEffect s
    _ -> return ()

ecVar :: HasCallStack => Id -> EcM TypeWithEffect
ecVar x | isBuiltinVar x = return $ builtinTwe [] $ nameBuiltinInfo $ varName x
ecVar x = do
  mt <- lookupUM x <$> asks _env
  case mt of
    Nothing -> ecIce $ "Variable \'" <> pretty x <> "\' not bound."
    Just res -> instantiateEffectsInTwe res

ecSetLoc :: Location -> EcM a -> EcM a
ecSetLoc l = locally loc (const l)

ecTypeOfId :: Id -> EcM (Type TyVar)
ecTypeOfId x = case idType x of
  TForAll [] _ t -> return t
  _ -> ecSetLoc (location x) $ ecIce "Unexpected universally quantified type."

ecUnique :: EcM Unique
ecUnique = do
  u <- gets _uniq
  uniq .= nextUnique u
  return u

ecFreshVar :: T.Text -> Kind -> EcM Var
ecFreshVar prefix k = do
  u <- ecUnique
  l <- asks _loc
  let name = mkName prefix u l
  let var = mkMetaTyVar name k 0
  return var

ecFreshEffectMetaVar :: EcM (EffectVar, Effect)
ecFreshEffectMetaVar = do
  v <- ecFreshVar "e" KindEffect
  unsolvedEffectVars `scribe` singletonUM' v
  return (v, mkEffectMetaVar v)

ecFreshEffectRigidVar :: EcM (EffectVar, Effect)
ecFreshEffectRigidVar = do
  u <- ecUnique
  i <- effectVarNum <+= 1
  l <- asks _loc
  let name = mkName (T.pack ("E" ++ show i)) u l
  let var = mkTyVar name KindEffect
  let ty = TVar var KindEffect l
  return (var, mkEffect ty)

-- Annotates function type with a single effect meta variable as follows:
--  t1 -> (t2 -> (t3 -> t4 ! eff) ! ø) ! ø
ecFreshTweMetaVarFun :: [TypeWithEffect] -> TypeWithEffect -> EcM (EffectVar, TypeWithEffect)
ecFreshTweMetaVarFun [] _ = ecIce "Expecting at least one function argument."
ecFreshTweMetaVarFun [t1] t2 = second (flip (TweFun t1 t2) []) <$> ecFreshEffectMetaVar
ecFreshTweMetaVarFun (t1 : ts) t2 = do
  (effVar, funTy) <- ecFreshTweMetaVarFun ts t2
  return (effVar, TweFun t1 funTy mempty [])

instantiateEffectsInTwe :: HasCallStack => ([EffectVar], TypeWithEffect) -> EcM TypeWithEffect
instantiateEffectsInTwe (xs, twe) = do
  vs <- mapM (\_ -> snd <$> ecFreshEffectMetaVar) xs
  let um = fromListUM (zip xs vs)
  return $ go um twe
  where
    goT um (TVar x KindEffect _)
      | Just eff <- lookupUM x um = eff
    goT _  t                      = mkEffect t

    goE um (Effect vs ts) =
      let
        effs = map (goT um) ts
      in
        Effect vs [] <> mconcat effs

    goC um (EffLe e1 e2 l) = EffLe (goE um e1) (goE um e2) l
    goC _  _               = error "Constraints other that EffLe should not occur in effect types"

    go um = \case
      TweAny -> TweAny
      TweTuple ts -> TweTuple $ map (go um) ts
      TweFun t1 t2 eff cs -> let
          t1' = go um t1
          t2' = go um t2
        in TweFun t1' t2' (goE um eff) (map (goC um) cs)

ecInstantiateType_ :: Type Var -> EcM TypeWithEffect
ecInstantiateType_ t = snd <$> ecInstantiateType t

ecInstantiateType :: Type Var -> EcM (Bag EffectVar, TypeWithEffect)
ecInstantiateType = \case
  TQualify u _ _ -> ecInstantiateType u
  funType@TFun{} -> do
    let (ts, t) = splitFuncType funType
    (ess, ts') <- unzip <$> mapM ecInstantiateType ts
    (es', t') <- ecInstantiateType t
    (effVar, funType') <- ecFreshTweMetaVarFun ts' t'
    let vars = mconcat ess <> es' <> singletonBag effVar
    return (vars, funType')
  TList t -> do
    (es, t') <- ecInstantiateType t
    return (es, TweTuple [t'])
  TArr t -> do
    (es, t') <- ecInstantiateType t
    return (es, TweTuple [t'])
  TStore k v -> do
    (es, k') <- ecInstantiateType k
    (es', v') <- ecInstantiateType v
    return (es <> es', TweTuple [k', v'])
  t -> do
    senv <- asks _structsEnv
    case tryGetFieldTypes senv t of
      Just ts -> do
        (ess, ts') <- unzip <$> mapM ecInstantiateType ts
        return (mconcat ess, TweTuple ts')
      Nothing -> return (emptyBag, TweAny)

typeOfExpr :: (Type TyVar -> Expr Var -> EcM a) -> Expr Var -> EcM a
typeOfExpr k = \case
  Ascription e t -> k t e
  TypeAnnot t e -> k t e
  ExprLoc l e -> ecSetLoc l $ typeOfExpr k e
  _ -> ecIce "Missing type annotation."

getExprType :: Expr Var -> EcM (Type TyVar)
getExprType = typeOfExpr (\t _ -> return t)

getArrElemType :: Type TyVar -> EcM (Type TyVar)
getArrElemType (TArr t) = return t
getArrElemType _        = ecThrow "Expecting array type"

ecSplitQualified :: Type a -> EcM (UnqualifiedType a, StageType a, DomainType a)
ecSplitQualified (TQualify u s d) = return (u, s, d)
ecSplitQualified t@(TVar _ KindStar _) = return (TGetUnqual t, TGetStage t, TGetDomain t)
ecSplitQualified _ = ecThrow "Expecting qualified type."

ecCollectEffects :: EcM a -> EcM (a, Effect)
ecCollectEffects = listens _effects

-- Pure function
infixr 5 -*>
(-*>) :: TypeWithEffect -> TypeWithEffect -> TypeWithEffect
t1 -*> t2 = TweFun t1 t2 mkEffectEmpty []

infixr 4 !
(!) :: TypeWithEffect -> Effect -> TypeWithEffect
TweFun t1 t2 _ cs ! e = TweFun t1 t2 e cs
_ ! _ = error "Unable to attach effect to non-functional value."

tweBinPrimFn :: HasCallStack => Type TyVar -> TypeWithEffect
tweBinPrimFn s = assert (typeKind s == KindStage) $
  TweAny -*> TweAny -*> TweAny ! mkEffect s

tweUnPrimFn :: Type TyVar -> TypeWithEffect
tweUnPrimFn s = TweAny -*> TweAny ! mkEffect s

tweAnyList :: TypeWithEffect
tweAnyList = TweTuple [TweAny]

vectorizeTwe :: TypeWithEffect -> EcM TypeWithEffect
vectorizeTwe TweAny
  = return $ TweTuple [TweAny]
vectorizeTwe (TweFun twefun twearg eff cs)
  = TweFun <$> vectorizeTwe twefun <*> vectorizeTwe twearg <*> pure eff <*> pure cs
vectorizeTwe _
  = ecThrow "Tuples or arrays cannot be vectorized."

builtinTwe :: [Type TyVar] -> BuiltinInfo -> TypeWithEffect
builtinTwe [_, s, _] BuiltinAdd = tweBinPrimFn s
builtinTwe [_, s, _] BuiltinSub = tweBinPrimFn s
builtinTwe [_, s, _] BuiltinMul = tweBinPrimFn s
builtinTwe _ BuiltinDiv = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinModDiv = TweAny -*>TweAny -*> TweAny
builtinTwe _ BuiltinMod = TweAny -*> TweAny -*> TweAny
builtinTwe [_, s, _] BuiltinXor = tweBinPrimFn s
builtinTwe [_, s, _] BuiltinAnd = tweBinPrimFn s
builtinTwe [_, s, _] BuiltinOr = tweBinPrimFn s
builtinTwe [_, s, _] BuiltinBoolXor = tweBinPrimFn s
builtinTwe [_, s, _] BuiltinNeg = tweUnPrimFn s
builtinTwe _ BuiltinEq = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinNeq = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinLt = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinLe = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinGt = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinGe = TweAny -*> TweAny -*> TweAny
builtinTwe [_n, s, _d] BuiltinCircuitCall =
  TweAny -*> TweTuple [TweTuple [TweAny]] -*> TweTuple [TweTuple [TweAny]] ! mkEffect s
builtinTwe [s, _d] BuiltinCircuitCallU =
  TweAny -*> tweAnyList -*> tweAnyList ! mkEffect s
builtinTwe [d, _n] BuiltinAssert = TweAny -*> TweAny ! mkEffect mkPost
-- multiple fields are not allowed in match cases, hence "All False":
builtinTwe [d, _t1, _t2] BuiltinAssertEq = TweAny -*> TweAny -*> TweAny ! mkEffect mkPost <> mkEffect mkFF
builtinTwe [_n, d] BuiltinAssertEqUintsBools = tweAnyList -*> tweAnyList -*> TweAny ! mkEffect mkPost
builtinTwe [d, _n] BuiltinAssertZero = TweAny -*> TweAny ! mkEffect mkPost
builtinTwe _ BuiltinChallenge = TweAny -*> tweAnyList ! mkEffect mkPublicDomain <> mkEffect mkFF
builtinTwe _ BuiltinLength = tweAnyList -*> TweAny
builtinTwe _ BuiltinMakeWaksmanNetwork = TweAny -*> tweAnyList
builtinTwe _ BuiltinGetSortingPermutation = tweAnyList -*> tweAnyList
builtinTwe _ BuiltinPermutationSwitches = tweAnyList -*> tweAnyList
builtinTwe _ BuiltinFieldBitWidth = TweAny -*> TweAny
builtinTwe _ BuiltinDbgPrint = TweAny -*> TweAny
builtinTwe _ BuiltinStringAppend = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinToString = TweAny -*> TweAny
builtinTwe _ BuiltinDefaultValue = TweAny -*> TweAny
builtinTwe _ BuiltinModInvert = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinConst = TweAny
builtinTwe [_n, s, _d, _dl] BuiltinFreeze = tweAnyList -*> tweAnyList ! mkEffect s
builtinTwe _ BuiltinThaw = tweAnyList -*> tweAnyList
builtinTwe _ BuiltinFlatten = tweAnyList -*> tweAnyList
builtinTwe _ BuiltinUnflatten = tweAnyList -*> tweAnyList -*> tweAnyList
builtinTwe _ BuiltinIndexTensor = tweAnyList -*> tweAnyList -*> TweAny
builtinTwe _ BuiltinIndexTensor1 = tweAnyList -*> TweAny -*> tweAnyList
builtinTwe _ BuiltinSize = tweAnyList -*> tweAnyList
builtinTwe _ BuiltinUnslice = tweAnyList -*> tweAnyList
builtinTwe [_u, d] BuiltinArrayToPost = tweAnyList -*> tweAnyList ! wireEffect d
builtinTwe _ BuiltinArrayToProver = tweAnyList -*> tweAnyList
builtinTwe _ BuiltinBitextractPreUint = TweAny -*> TweAny -*> tweAnyList
builtinTwe _ BuiltinBitextractVecHelper = tweAnyList -*> TweAny -*> tweAnyList ! mkEffect mkPost
builtinTwe _ BuiltinMakeUnknown = TweAny -*> TweAny
builtinTwe _ BuiltinMakeNotUnknown = TweAny -*> TweAny -*> TweAny
builtinTwe _ BuiltinUintNPreMatrixProd = tweAnyList -*> tweAnyList -*> tweAnyList
builtinTwe _ BuiltinPluginLT = TweAny -*> TweAny -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginLE = TweAny -*> TweAny -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginDiv = TweAny -*> TweAny -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginDivMod = TweAny -*> TweAny -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginBitextract = TweAny -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginAssertPerm = tweAnyList -*> tweAnyList -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginAdd = tweAnyList -*> tweAnyList -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginMul = tweAnyList -*> tweAnyList -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginAddC = tweAnyList -*> TweAny -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginMulC = tweAnyList -*> TweAny -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginAddScalar = tweAnyList -*> TweAny -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginMulScalar = tweAnyList -*> TweAny -*> tweAnyList ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginSum = tweAnyList -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginProd = tweAnyList -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ BuiltinPluginDotProd = tweAnyList -*> tweAnyList -*> TweAny ! mkEffect mkPublicDomain
builtinTwe _ _ = error "Ill formed primitive."

ecFunTwe :: IsVectorized -> [Type TyVar] -> Var -> EcM (Maybe TypeWithEffect)
ecFunTwe _ ts f
  | isGetInput = do
    Just resultType <- asks _resultType
    resultTwe <- ecInstantiateType_ resultType
    dom <- case builtin of
        BuiltinGetPublic -> return mkPublicDomain  -- TODO: should this actually have an effect?
        BuiltinGetInstance -> do
          effects `scribe` mkEffect mkFF
          return mkVerifierDomain
        BuiltinGetWitness -> return mkProverDomain
        _ -> ecIce "Unreachable."
    return $ Just $ TweAny -*> resultTwe ! mkEffect dom
  | isBuiltin = return $ Just $ builtinTwe ts builtin
  | otherwise = do
    mres <- lookupUM f <$> asks _env
    case mres of
      Nothing -> return Nothing
      Just res -> Just <$> instantiateEffectsInTwe res
  where
    isBuiltin = isBuiltinVar f
    builtin = nameBuiltinInfo $ varName f
    isGetInput = isBuiltin && builtin `elem` [BuiltinGetInstance, BuiltinGetWitness, BuiltinGetPublic]

ecTypeEff
  :: QualifiedType Var -> EcM Effect
ecTypeEff t
  = let
      ecStagesDomains t
        = do
            (u , s , d) <- ecSplitQualified t
            let standard = (s :) . (d :)
            case u of
              TUnit
                -> return id
              TBool _
                -> return standard
              TUInt _
                -> return standard
              TString
                -> return (d :)
              TList _
                -> return (d :)
              TArr _
                -> return (d :)
              TFun _ _
                -> return standard
              TCast _ _
                -> return standard
              TCastUnqual _ _
                -> return standard
              TCastStage _ _
                -> return standard
              TCastDomain _ _
                -> return standard
              TStore _ _
                -> return standard
              TGetUnqual _
                -> return standard
              t -> do
                     senv <- asks _structsEnv
                     case tryGetFieldTypes senv t of
                       Just ts
                         -> foldr (.) id <$> traverse ecStagesDomains ts
                       _ -> case t of
                              TVar _ _ _
                                -> return standard
                              TApp (TVar _ _ _) _ _
                                -> return standard
                              _ -> ecIce ("ecDomainEff: Unexpected type" <+> pretty t)
    in
    mconcat . fmap mkEffect . ($ []) <$> ecStagesDomains t

ecInferExpr :: Expr Var -> EcM (Type Var , TypeWithEffect)
ecInferExpr e = do
  ty <- getExprType e
  (effVars, twe) <- ecInstantiateType ty
  effects `scribe` mconcat (map mkEffectMetaVar (toList effVars))
  locally resultType (const (Just ty)) $ ecExpr twe e
  return (ty , twe)

ecInferExpr_ :: Expr Var -> EcM TypeWithEffect
ecInferExpr_ e
  = snd <$> ecInferExpr e

ecCtrl
  :: ([Expr Var] , Type Var) -> ([Expr Var] , Type Var) -> EcM ([TypeWithEffect] , [TypeWithEffect])
ecCtrl (heads , headQTy) (bodys , bodyQTy)
  = do
      (_, _, d') <- ecSplitQualified headQTy
      headTys <- traverse ecInferExpr_ heads
      (bodyTys , bodyEff) <- ecCollectEffects $ traverse ecInferExpr_ bodys
      resultEff <- ecTypeEff bodyQTy
      l <- asks _loc
      constraints `scribe` [EffLe (mkEffect d') (eliminatePosts [resultEff, bodyEff]) l]
      return (headTys , bodyTys)

substRigidTypeVarsInTwe :: UniqMap (Type TyVar) -> TypeWithEffect -> TypeWithEffect
substRigidTypeVarsInTwe um = go
  where
    go = \case
      TweAny -> TweAny
      TweTuple ts -> TweTuple (map go ts)
      TweFun t1 t2 eff cs -> TweFun (go t1) (go t2) (substRigidTypeVarsInEffect um eff)
                                    (map (substRigidTypeVarsInEffConstraint um) cs)

substRigidTypeVarsInEffect :: UniqMap (Type TyVar) -> Effect -> Effect
substRigidTypeVarsInEffect um (Effect xs ts) = mconcat (Effect xs tsOld : map mkEffect tsNew)
  where
    (tsNew, tsOld) = partitionEithers $ map tryApply ts
    tryApply = \case
      TVar x _ _ | Just t <- lookupUM x um -> Left t
      t -> Right t

substRigidTypeVarsInEffConstraint :: UniqMap (Type TyVar) -> EffConstraint -> EffConstraint
substRigidTypeVarsInEffConstraint um = \case
  EffLe e1 e2 l -> EffLe (substRigidTypeVarsInEffect um e1) (substRigidTypeVarsInEffect um e2) l
  EffEq e1 e2 l -> EffEq (substRigidTypeVarsInEffect um e1) (substRigidTypeVarsInEffect um e2) l
  EffUnify t1 t2 l -> EffUnify (substRigidTypeVarsInTwe um t1) (substRigidTypeVarsInTwe um t2) l

ecExpr :: TypeWithEffect -> Expr Var -> EcM ()
ecExpr ty = \case
  Ascription e _ -> ecExpr ty e
  TypeAnnot _ e -> ecExpr ty e
  Assign iv e1 e2 -> do
    t1 <- ecInferExpr_ e1
    (q , t2) <- ecInferExpr e2
    q' <- if iv == IsVectorized
            then do
                   (u, _, _) <- ecSplitQualified q 
                   getArrElemType u 
            else return q
    eff <- ecTypeEff q'
    effects `scribe` eff
    ecUnifyTwe t1 t2
  Block stmts mresExpr -> ecBlock ty stmts mresExpr
  Call _ Method{} _typeArgs _es -> ecIce "TODO: method calls not implemented"
  Call iv (Func (Located l f)) typeArgs es -> do
    ts <- forM typeArgs $ \case
      TypeArg t -> return t
      _ -> ecIce "Ill formed type arguments. Should have been desugared away."
    if isId f
      then do
        let vectorizedOrNot = if iv == NotVectorized then return else vectorizeTwe
        mFunEffType <- ecFunTwe iv ts f
        funEffType <- case mFunEffType of
          Nothing -> ecSetLoc l $ ecIce "Expecting a function type."
          Just t -> return t {- this twe is already instantiated -} 
        let subst = typeSchemeApply (idType f) ts
        funEffType' <- vectorizedOrNot $ substRigidTypeVarsInTwe subst funEffType
        let numArgs = if null es then 1 else length es -- TODO: Frustraitingly wonky.
        let (argTys, resultTy, effs, cs) = splitFunTwe funEffType' numArgs
        argTys' <- mapM ecInferExpr_ es
        ecUnifyTwe resultTy ty
        zipWithM_ ecUnifyTwe argTys argTys'
        effects `scribe` effs
        constraints `scribe` cs
      else
        ecIce "Expecting identifier in function call"
  Cast e t -> do
    origt <- getExprType e
    (_, s, _) <- ecSplitQualified origt
    void (ecInferExpr e)
    let b = isFieldConv origt t
    effects `scribe` ((if b then mkEffect s else mkEffectEmpty) <> mkEffect (mkKBool (not (b && isPostStage s))))
  {-
    We are not doing any checks here because necessary stuff is already covered by the type checker.
    1. <d> <= <d'> is directly covered during previous phase.
    2. <d'> <= <u> is not checked because it breaks some common patterns.
       For instance this would break converting `list[uint $post @prover] @public` to `list[uint $post @prover] @prover`.
       We always allow forgetting information and this case some parties just forget length of the list
       while they clearly know it. For example $post elements are known publicly in this case.
  -}
  DbgAssert e me -> do
    mapM_ ecInferExpr_ (e : maybeToList me)
    -- (_, _, d) <- ecSplitQualified =<< getExprType e
    -- effects `scribe` mkEffect d
  DbgAssertEq e1 e2 me -> do
    mapM_ ecInferExpr_ (e1 : e2 : maybeToList me)
    -- (_, _, d) <- ecSplitQualified =<< getExprType e1
    -- effects `scribe` mkEffect d
  For (Located _ x) e1 e2 e3 -> ecForExpr ty x e1 e2 e3
  IfThenElse e1 e2 e3 -> do
    -- TODO: the following code is pretty ugly
    t1 <- getExprType e1
    void (ecInferExpr e1)
    ((_, ds2), bc2) <- listens _breakContexts $ ecCollectEffects $ ecExpr ty e2
    ((_, ds3), bc3) <- listens _breakContexts $ ecCollectEffects $ traverse (ecExpr ty) e3
    (_, _, d') <- ecSplitQualified t1
    unless (null bc2 && null bc3) $ breakContexts `scribe` [d']
    q <- getExprType e2
    resultEff <- ecTypeEff q
    l <- asks _loc
    constraints `scribe` [EffLe (mkEffect d') (eliminatePosts [resultEff, ds2, ds3]) l]
  IndexStore e1 e2 -> do
    tStore <- ecInferExpr_ e1
    tKey <- ecInferExpr_ e2
    (_, s, _) <- ecSplitQualified =<< getExprType e1
    -- This adds effect <s> to both store reads and writes.
    -- Although later <s> + <d> is added for writes, it does not hurt to add <s> twice.
    effects `scribe` mkEffect s
    ecUnifyTwe tStore (TweTuple [tKey, ty])
  Index e1 (Located l slice) -> do
    t1 <- ecInferExpr_ e1
    ecSetLoc l $
      traverse_ ecInferExpr_ slice
    {- -- Indexing may cause out-of-bounds error
    q <- getExprType e1
    (_, _, d) <- ecSplitQualified q
    effects `scribe` mkEffect d
    -}
    case slice of
      ArrayIndex _ -> ecUnifyTwe t1 (TweTuple [ty])
      _ -> ecUnifyTwe t1 ty
  Lam _ params _ e -> do
    let xs = map (unLocated._lamParamName) params
    let ts = map (fromJust._lamParamType) params
    twes <- mapM ecInstantiateType_ ts
    (resTy, effs) <- locally env (insertManyUM [(x, ([], twe)) | (x, twe) <- zip xs twes]) $
      clearing effects $
        ecCollectEffects $
          ecInferExpr_ e
    ecUnifyTwe (mkFunTwe twes resTy effs) ty
  List list -> case list of
    ListReplicate e1 e2 -> do
      q1 <- getExprType e1
      q2 <- getExprType e2
      (_, t1) <- ecCtrl ([e2], q2) ([e1], q1)
      ecUnifyTwe (TweTuple t1) ty
    _ -> do
           Just (q@(TQualify (TList q1) _ _)) <- asks _resultType
           (_, ts) <- ecCtrl ([], q) (toListOf elemsInList list, q1)
           traverse_ (\ t -> ecUnifyTwe (TweTuple [t]) ty) ts
  Lit con -> ecLit con
  Match e cases -> do
    t <- getExprType e
    t1 <- maybe (ecIce "ecExpr: Match expression with no result type") return =<< asks _resultType
    (_, _, d') <- ecSplitQualified t
    void (ecInferExpr e)
    dss <- fmap snd <$> traverse (ecCollectEffects . ecCase ty) cases
    resultEff <- ecTypeEff t1
    l <- asks _loc
    constraints `scribe` [EffLe (mkEffect d') (removeStages (resultEff : dss)) l]
  RefArg e -> ecExpr ty e
  Select e sel -> do
    structTy <- getExprType e
    t <- ecInferExpr_ e
    ts <- case t of
      TweTuple ts' -> return ts'
      _ -> ecIce $ "Expecting structural type." <+> pretty structTy <+> pretty t
    senv <- asks _structsEnv
    case tryGetFieldPos senv structTy sel of
      Nothing -> ecIce "Ill formed struct."
      Just i -> ecUnifyTwe (ts !! i) ty
  Self -> ecIce $ "Self not implemented."
  StoreCtor kvs -> do
    forM_ kvs $ \(ek, ev) -> do
      tk <- ecInferExpr_ ek
      tv <- ecInferExpr_ ev
      ecUnifyTwe ty $ TweTuple [tk, tv]
  StructCtor _ _ fields -> do
    -- struct fields are ordered during type checking
    t <- TweTuple <$> mapM (ecInferExpr_ . _structFieldCtorExpr) fields
    ecUnifyTwe t ty
  Tuple es -> do
    t <- TweTuple <$> mapM ecInferExpr_ es
    ecUnifyTwe t ty
  Var (Located l x) -> do
    t <- ecSetLoc l $ ecVar x
    ecUnifyTwe t ty
  While e1 e2 -> do
    q1 <- getExprType e1
    q2 <- getExprType e2
    (_, _, d') <- ecSplitQualified q1
    ds1 <- snd <$> ecCollectEffects (ecInferExpr e1)
    (ds, bc) <- clearing breakContexts $ listens _breakContexts $ snd <$> ecCollectEffects (ecInferExpr e2)
    resultEff <- ecTypeEff q2
    l <- asks _loc
    constraints `scribe` map (\ d' -> EffLe (mkEffect d') (eliminatePosts [resultEff, ds1, ds]) l) (d' : bc)
  WireExpr shape e -> do
    _ <- ecInferExpr shape
    _ <- ecInferExpr e
    q <- getExprType e
    (_, _, d) <- ecSplitQualified q
    effects `scribe` wireEffect d
  Zip pairs e -> do
    (_, _, d) <- ecSplitQualified =<< fromJust <$> asks _resultType
    let (xs, xss) = unzip pairs
    forM_ xss ecInferExpr
    q <- getExprType e
    resultEff <- ecTypeEff q
    (t0, eff0) <- ecCollectEffects $ locally env (insertManyUM [(x, ([], TweAny)) | Located _ x <- xs]) $ ecInferExpr_ e
    l <- asks _loc
    constraints `scribe` [EffLe (mkEffect d) (eliminatePosts [resultEff, eff0]) l]
    ecUnifyTwe ty (TweTuple [t0])
  ExprLoc l e -> ecSetLoc l $ ecExpr ty e
  TypeIf (TypePred PConPost [TVar s KindStage _] _) e1 e2 -> do
    flip (censoring constraints) (ecExpr ty e1) $ map (substRigidTypeVarsInEffConstraint (singletonUM s mkPost))
    flip (censoring constraints) (ecExpr ty e2) $ map (substRigidTypeVarsInEffConstraint (singletonUM s mkPre))
  TypeIf (TypePred PConPre [TVar s KindStage _] _) e1 e2 -> do
    flip (censoring constraints) (ecExpr ty e1) $ map (substRigidTypeVarsInEffConstraint (singletonUM s mkPre))
    flip (censoring constraints) (ecExpr ty e2) $ map (substRigidTypeVarsInEffConstraint (singletonUM s mkPost))
  TypeIf _ e1 e2 -> ecExpr ty e1 >> ecExpr ty e2 -- this is ok because both branches must have identical types
  TypePredExpr _ -> return ()
  TypeToExpr _ -> return ()
  Trace _ e -> ecExpr ty e
  CallOper _ _ _ -> ecIce "CallOper should have been desugared away."
  Hole -> return ()

ecBlock :: TypeWithEffect -> [Stmt Var] -> Maybe (Expr Var) -> EcM ()
ecBlock resTy statementList mresExpr = go statementList
  where
    go [] = forM_ mresExpr (ecExpr resTy)
    go (stmt : stmts) = ecStmt stmt (go stmts)

ecStmt :: Stmt Var -> EcM a -> EcM a
ecStmt (Expr e) cont = do
  case viewForExpr e of
    Just (x, e1, e2, e3) -> ecForStmt x e1 e2 e3
    Nothing -> void (ecInferExpr e)
  cont
ecStmt (Let _ (Binding _ (Located l x) mt) e) cont = ecSetLoc l $ do
  let Just t = mt
  twe <- ecInstantiateType_ t
  locally env (insertUM x ([], twe)) $ do
    twe' <- ecInferExpr_ e
    ecUnifyTwe twe twe'
    cont
ecStmt (Break _) cont = (breakContexts `scribe` [mkPublicDomain]) >> cont
ecStmt (Continue _) cont = (breakContexts `scribe` [mkPublicDomain]) >> cont
ecStmt (Return e) cont = do
  -- TODO: return has effect but it's only a local one
  -- we should verify (in type checking phase) that return is only ever called from
  -- inside public control flow
  _ <- ecInferExpr e
  cont

ecForStmt :: Located Var -> Expr Var -> Expr Var -> Expr Var -> EcM ()
ecForStmt (Located _ x) e1 e2 e3 = do
  (_, _, d') <- ecSplitQualified =<< ecTypeOfId x
  _ <- ecInferExpr e1
  _ <- ecInferExpr e2
--   (_, _, d1) <- ecSplitQualified q1
--   (_, _, d2) <- ecSplitQualified q2
  ((_, eff), bc) <- clearing breakContexts $ listens _breakContexts $ ecCollectEffects $ locally env (insertUM x ([], TweAny)) $ ecInferExpr e3
  l <- asks _loc
  constraints `scribe` map (\ d -> EffLe (mkEffect d) (eliminatePosts [eff]) l) (d' : bc)

ecForExpr :: TypeWithEffect -> Var -> Expr Var -> Expr Var -> Expr Var -> EcM ()
ecForExpr resTy x e1 e2 e3 = do
  q <- ecTypeOfId x
  (_, _, d') <- ecSplitQualified q
  _ <- ecInferExpr e1
  _ <- ecInferExpr e2
--   q3 <- getExprType e3
--   (_, _, d1) <- ecSplitQualified q1
--   (_, _, d2) <- ecSplitQualified q2
  ((q3 , t3) , eff) <- ecCollectEffects $ locally env (insertUM x ([], TweAny)) $ ecInferExpr e3
  resultEff <- ecTypeEff q3
  l <- asks _loc
  constraints `scribe` [EffLe (mkEffect d') (eliminatePosts [resultEff, eff]) l]
  ecUnifyTwe resTy (TweTuple [t3])

ecCase
  :: TypeWithEffect -> (Located (Pat Var), Expr Var) -> EcM ()
ecCase resTy (p , e)
  = do
      eff <- fmap snd . ecCollectEffects $ 
             case unLocated p of
               VarPat x
                 -> locally env (insertUM x ([], TweAny)) $ ecExpr resTy e
               _ -> ecExpr resTy e
      if isFFEff eff
        then ecThrow (pretty forbiddenOperErrMsg)
        else do
               l <- asks _loc
               constraints `scribe` [EffLe (mkEffect (mkCon ConNoDomain)) (extractKBoolVars [eff]) l]

ecInstantiateSignature
  :: Id -> [SimpleFuncParam Id] -> EcM (Bag EffectVar, ([EffectVar], TypeWithEffect), [TypeWithEffect], Type TyVar, EffectVar)
ecInstantiateSignature f params 
  = do
      let arity = if null params then 1 else length params
      let TForAll _ _ funType = idType f
      let (ts, t) = splitFuncTypeN funType arity
      (x, es, ts', funTy) <- ecSignatureToTwe ts t
      return (es, funTy, ts', t, x)

-- When effect checking a group of recursive functions fails we still
-- want to continue typing rest of the code.
-- For that we need to make up effect signature for those functions.
-- What signature do we pick?
-- Effect at the output position should be missing.
-- Effects at input positions should be as little restricted as possible. It's either
-- < @public > or quantified universally.
-- To put it concretely:
-- foo :! (prim -> prim ! < @public >) -> prim ! ø
-- foo :! forall E. (prim -> prim ! E) -> prim ! ø

-- bad_binary :! prim -> (prim -> prim ! ø) ! ø
-- bad_higher_rank :! ((prim -> prim ! ø) -> prim ! E) -> ø

ecSignatureToTwe ::  [Type Var] -> Type Var -> EcM (EffectVar, Bag EffectVar, [TypeWithEffect], ([EffectVar], TypeWithEffect))
ecSignatureToTwe ts t = do
  effectVarNum .= 0
  (vs, ts') <- unzip <$> mapM (go False) ts
  (v1, t') <- go True t
  let (xs, ys) = v1 <> mconcat vs
  (x, e) <- ecFreshEffectMetaVar
  return (x, singletonBag x <> xs, ts', (toListBag ys, mkFunTwe ts' t' e))
  where
    makeMostGeneralEffect inRetPos =
      if inRetPos
        then do
          (x, e) <- ecFreshEffectMetaVar
          return ((singletonBag x, emptyBag), e)
        else do
          (x, e) <- ecFreshEffectRigidVar
          return ((emptyBag, singletonBag x), e)
    go inRetPos = \case
      TQualify u _ _ -> go inRetPos u
      TList t -> do
        (es, t') <- go inRetPos t
        return (es, TweTuple [t'])
      TArr t -> do
        (es, t') <- go inRetPos t
        return (es, TweTuple [t'])
      TStore k v -> do
        (es, k') <- go inRetPos k
        (es', v') <- go inRetPos v
        return (es <> es', TweTuple [k', v'])
      funType@TFun{} -> do
        let (ts, t) = splitFuncType funType
        (ess, ts') <- unzip <$> mapM (go (not inRetPos)) ts
        (es', t') <- go inRetPos t
        (es'', eff) <- makeMostGeneralEffect inRetPos
        let vars = mconcat ess <> es' <> es''
        return (vars, mkFunTwe ts' t' eff)
      t -> do
        senv <- asks _structsEnv
        case tryGetFieldTypes senv t of
          Just ts -> do
            (ess, ts') <- unzip <$> mapM (go inRetPos) ts
            return (mconcat ess, TweTuple ts')
          Nothing -> return ((emptyBag, emptyBag), TweAny)

ecExtern :: TypedTopExtern -> EcM () -> EcM ()
ecExtern ext cont = do
  let extName = _tExtName ext
--   let extLoc = location extName
  (toList -> signEffectVars, t, _, _, _) <- ecInstantiateSignature extName (_tExtArgs ext)
  annot <- case _tExtEff ext of
    Just (Located _ e) -> do
      verbosePrint $ "* Effect annotation for" <+> pretty extName <> ":" <+> pretty e
      return $ Just e
    Nothing            -> return Nothing
  let unsolvedEffVars = fromListUM' signEffectVars
  unless (null unsolvedEffVars) $ do
    verbosePrint "* Residual effect vars:"
    mapM_ (\ c -> verbosePrint ("  " <> pretty c)) (toList unsolvedEffVars)
  let allEffSubst = mapUM (const mkEffectEmpty) unsolvedEffVars
  let t2 = second (tweApplySubsts allEffSubst) t
  let 
    t' = case annot of
           Just (PolyTwe es funTy) -> (es, funTy)
           _                       -> t2
  printEffectTypes <- asks _debugPrintEffectTypes
  when printEffectTypes $ do
    (es, funTy) <- return t'
    let forallDoc = if null es then "" else "∀" <+> hcat (punctuate " " (map pretty es)) <+> ". "
    liftIO $ putStrLn $ render $ pretty extName <+> ":!" <+> forallDoc <> pretty funTy
  verbosePrint ("*" <+> pretty extName <+> ":!" <+> pretty t')
  clearing unsolvedEffectVars . clearing constraints . locally env (insertUM extName t') $ cont

-- Derives the effect types for a group of mutually recursive functions.
-- And continues the rest of the effect checking with `cont`.
-- The continuation has access to derived types.
ecMutuallyRecursiveFunctions :: [TypedTopFunction] -> EcM () -> EcM ()
ecMutuallyRecursiveFunctions fs cont = do
  let funNames = [f | TypedTopFunction f _ _ _ _ _ <- fs]
  let funLocs = map location funNames
  (toList.mconcat -> signEffectVars, ts, argTypes, retTypes, effVars) <-
    unzip5 <$> zipWithM ecInstantiateSignature funNames (_tFunArgs <$> fs)
  let funcEnv = fromListUM (zip funNames (map (first (const [])) ts))
  ((_, cs), unsolvedEffVars) <- listening unsolvedEffectVars $
    listening constraints $
      locally env (`unionUM` funcEnv) $
        forM_ (zip4 argTypes retTypes effVars fs) $ \(argTys, _, effVar, TypedTopFunction{..}) -> do
          let xs = [x | SimpleFuncParam _ x <- _tFunArgs]
          let varEnv = fromListUM [(x, ([], argTy)) | (x, argTy) <- zip xs argTys]
          (_, eff) <- listening effects $
            locally env (`unionUM` varEnv) $
              ecIgnoreEx $
                ecInferExpr _tFunBody
          constraints `scribe` [EffEq (mkEffectMetaVar effVar) eff (location _tFunName)]
  verbosePrint $ "\n\nEffect check functions:" <+> pretty funNames
  annots <- forM fs $ \ f ->
    case _tFunEff f of
      Just (Located _ e) -> do
        verbosePrint $ "* Effect annotation for" <+> pretty (_tFunName f) <> ":" <+> pretty e
        return $ Just e
      Nothing -> return Nothing
  let allAnnotated = all isJust annots
  verbosePrint $ "* Instantiated types:     " <+> pretty ts
  verbosePrint $ "* Effect vars (system):   " <+> pretty (toList unsolvedEffVars)
  verbosePrint $ "* Effect vars (signature):" <+> pretty (toList signEffectVars)
  verbosePrint   "* Generated constraints:"
  mapM_ (\c -> verbosePrint ("  " <> pretty c)) cs
  unsolvedEffVars <- return $ fromListUM' signEffectVars <> unsolvedEffVars
  (effSubst, cs) <- return $ ecSolve cs
  verbosePrint   "* Solved constraints (phase 1):"
  mapM_ (\c -> verbosePrint ("  " <> pretty c)) cs
  let contradictions = filter (null . constrGetVars) cs
  if not (null contradictions)
    then messages `scribe` singletonBag (errMsg ("Unsolvable effect constraint" <+> pretty (head contradictions)) [])
    else do
           (effSubst, cs) <- return $ first (effSubst <>) $ ecMostGeneralSolution cs -- NOTE: return is needed for overshadowing!
           (effSubst, cs) <- if null cs
             then return (effSubst, cs)
             else do
               mres <- tryGuessingSolution cs
               case mres of
                 Nothing -> return (effSubst, cs)
                 Just (guessingSubst, cs) -> do
                   unless allAnnotated $ unless (all isEmptyEffect guessingSubst) $
                     messages `scribe` singletonBag (warnMsg "Found effect type by guessing. Inferred types might not be as generic as expected." funLocs)
                   return (effSubst <> guessingSubst, cs)
           let isMainFunction = case funNames of [f] -> nameOccName (varName f) == mainFName; _ -> False
           let (csPropagatable, csUnpropagatable) = if isMainFunction then ([], cs) else partition isConstraintPropagatable cs
           unless (null csPropagatable) $ do
             --unless allAnnotated $ do
             verbosePrint "* Unsolved constraints that can be propagated!"
             mapM_ (\c -> verbosePrint ("  " <> pretty c)) csPropagatable
           unless (null csUnpropagatable) $ do
             -- Suppress the warning if all functions have effect annotations
             unless allAnnotated $ messages `scribe` singletonBag (warnMsg "Unsolved effect constraints" (map location cs))
             verbosePrint "* Unsolved constraints that CANNOT be propagated!"
             mapM_ (\c -> verbosePrint ("  " <> pretty c)) csUnpropagatable
           unsolvedEffVars <- return $ filterUM (\x -> not (memberUM x effSubst)) unsolvedEffVars
           unless (null unsolvedEffVars) $ do
             verbosePrint "* Residual effect vars:"
             mapM_ (\c -> verbosePrint ("  " <> pretty c)) (toList unsolvedEffVars)
           let effSubst' = mapUM (const mkEffectEmpty) unsolvedEffVars
           let allEffSubst = effSubst <> effSubst'
           let
             addConstraints (TweFun t1 t2 e cs0) = TweFun t1 t2 e (csPropagatable ++ cs0)
             addConstraints t = t -- this case should not happen
           let ts2 = map (second (addConstraints . tweApplySubsts allEffSubst)) ts
           let
             ts' = flip map (zip ts2 annots) $ \ (t, annot) ->
               case annot of
                 Just (PolyTwe es funTy) -> (es, funTy)
                 Nothing -> t
           printEffectTypes <- asks _debugPrintEffectTypes
           when printEffectTypes $
             forM_ (zip funNames ts') $ \(name, (es, funTy)) -> do
               let forallDoc = if null es then "" else "∀" <+> hcat (punctuate " " (map pretty es)) <+> ". "
               liftIO $ putStrLn $ render $ pretty name <+> ":!" <+> forallDoc <> pretty funTy
           zipWithM_ (\name t -> verbosePrint ("*" <+> pretty name <+> ":!" <+> pretty t)) funNames ts'
           let funEnv' = fromListUM $ zip funNames ts'
           clearing unsolvedEffectVars $
             clearing constraints $
               locally env (`unionUM` funEnv')
                 cont

ecProg :: TypedProgram -> EcM ()
ecProg TypedProgram{..}
  = do
      msgs <- fmap snd . listening messages . foldr (.) id (fmap ecExtern _tProgExterns) $ go _tProgFunctions (return ())
      if hasErrMsg msgs
        then ecFail msgs
        else return ()
  where
    go [] act = act
    go (fs : fss) act = do
      ecMutuallyRecursiveFunctions (Data.Foldable.toList fs) $
        go fss act

ecModules :: TypedProgram -> Bool -> Bool -> Unique -> StructsEnv -> IO (Either Messages Unique)
ecModules prog v verbosePrintEffectTypes u senv = right snd <$> runEcM (ecProg prog) v verbosePrintEffectTypes u senv


-------------------------------
-- Effect constraint solving --
-------------------------------

-- Assumes that TVProver < TVNoDomain
isConstraintPropagatable :: EffConstraint -> Bool
isConstraintPropagatable (EffLe (Effect [] ts1) (Effect _ ts2) _) = go TVNoDomain ts1 ts2 where
  go d1 (TDomain d2 : ts1) ts2 = go (min d1 d2) ts1 ts2
  go _ (_ : _) _ = True
  go _ [] [] = True
  go d1 [] (TDomain d2 : _) | d1 > d2 = False
  go d1 [] (_ : ts2) = go d1 [] ts2
isConstraintPropagatable EffLe{} = True
isConstraintPropagatable _ = False

data EffSimpResult
  = EffSimpResultSplit [EffConstraint]
  | EffSimpResultUnifyEffect EffectVar Effect
  | EffSimpResultDelay -- unable to solve now, but could still progress later

simpEffC :: EffConstraint -> EffSimpResult
simpEffC c = case c of
  (EffUnify t1 t2 _) -> case (t1, t2) of
    (TweAny, _) -> EffSimpResultSplit []
    (_, TweAny) -> EffSimpResultSplit []
    (TweTuple ts, TweTuple ts') -> EffSimpResultSplit (zipWith effUnify ts ts')
    (TweFun a1 b1 e1 [], TweFun a2 b2 e2 []) -> EffSimpResultSplit [effUnify a1 a2, effUnify b1 b2, effEq e1 e2]
    (TweFun{}, TweFun{}) -> error "Constraints not yet supported in higher-order function effect types"
    _ -> EffSimpResultDelay
  (EffEq e1 e2 _) -> simpEffEq e1 e2
  (EffLe e1 e2 l) -> simpEffLe e1 e2 l
  where
    effEq e1 e2 = EffEq e1 e2 (location c)
    effUnify t1 t2 = EffUnify t1 t2 (location c)

simpEffEq :: Effect -> Effect -> EffSimpResult
simpEffEq (Effect xs ts) (Effect xs' ts') | xs == xs' && ts == ts' = EffSimpResultSplit []
simpEffEq (Effect [x] []) e2@(Effect [] _) = EffSimpResultUnifyEffect x e2
simpEffEq  e1@(Effect [] _) (Effect [x] []) = EffSimpResultUnifyEffect x e1
simpEffEq _ _ = EffSimpResultDelay

simpEffLe :: Effect -> Effect -> Location -> EffSimpResult
simpEffLe (Effect [] _) (Effect [] []) _ = EffSimpResultSplit []
simpEffLe (Effect xs ts) (Effect xs' ts') _ | xs == xs' && ts == ts' = EffSimpResultSplit []
simpEffLe (Effect _ ts) (Effect _ _) _ | any (isDomain TVPublic) ts = EffSimpResultSplit []
simpEffLe (Effect [] [TDomain d]) (Effect [] [TDomain d']) _ | d <= d' = EffSimpResultSplit []
simpEffLe (Effect [x] []) (Effect [] ts) _
  | Just pubDom <- find (isDomain TVPublic) ts = EffSimpResultUnifyEffect x (mkEffect pubDom)
simpEffLe e1@(Effect [] []) (Effect [x] []) _ = EffSimpResultUnifyEffect x e1
simpEffLe e1@(Effect [] []) (Effect xs []) l = EffSimpResultSplit [EffLe e1 (mkEffectMetaVar x) l | x <- xs]
simpEffLe _ _ _ = EffSimpResultDelay

headF :: Foldable f => f a -> First a
headF =  foldMap (First . Just)

-- Try to solve via x = ø and if that fails then x = < @public >
-- TODO: We could make more progress by calling `ecMostGeneralSolution` too!
tryGuessingSolution :: [EffConstraint] -> EcM (Maybe (UniqMap Effect, [EffConstraint]))
tryGuessingSolution [] = return $ Just (emptyUM, [])
tryGuessingSolution cs = case getFirst (foldMap headF cs) of
  Nothing -> return Nothing -- got unsolved constraints yet no free variables to substitute
  Just x -> do
    mZero <- guess x mkEffectEmpty
    case mZero of
      Just res -> return $ Just res
      Nothing -> guess x (mkEffect mkPublicDomain)
  where
    guess x e = do
      let cs' = fmap (effCApplySubst x e) cs
      let (subst, cs'') = ecSolve cs'
      fmap (first (insertUM x e subst <>)) <$> tryGuessingSolution cs''

-- For x ⊇ e_1, ..., x ⊇ e_n assume that we can pick x ~ e_1 + ... + e_n.
-- Each e_i may not contain effect meta variables.
-- We exclude meta variables that are multipli on the left side.
-- For example x_1 + x_2 ⊇ e blacklists x_1 and x_2.
ecMostGeneralSolution :: [EffConstraint] -> (UniqMap Effect, [EffConstraint])
ecMostGeneralSolution = go emptyUM
  where
    collect um bs [] = foldr deleteUM um bs
    collect um bs (EffLe (Effect [x] []) e _ : cs)
      | effectHasNoMetaVars e = collect (insertWithUM (<>) x e um) bs cs
    collect um bs (EffLe (Effect xs []) _ _ : cs)
      | length xs > 1 = collect um (insertManyUM [(x, x) | x <- xs] bs) cs
    collect um bs (_ : cs) = collect um bs cs

    go um cs
      | nullUM esub = (um, cs)
      | otherwise = go (um `unionUM` esub `unionUM` esub') cs''
      where
        esub = collect emptyUM emptyUM cs
        cs' = fmap (effCApplySubsts esub) cs
        (esub', cs'') = ecSolve cs'

ecSolve :: [EffConstraint] -> (UniqMap Effect, [EffConstraint])
ecSolve = go emptyUM [] False
  where
    go um acc b [] = if b
      then go um [] False (reverse acc)
      else (um, reverse acc)
    go um acc b (c : cs) = case simpEffC c of
      EffSimpResultSplit cs' -> go um acc True (cs' ++ cs)
      EffSimpResultDelay -> go um (c : acc) b cs
      EffSimpResultUnifyEffect x e -> go (insertUM x e um) acc True (fmap (effCApplySubst x e) cs)
