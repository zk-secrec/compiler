{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Core.LambdaLifting (
    coreLambdaLift,
    freeVarsInCoreLet,
)
where

import Basic.Location
import Basic.Name
import Basic.Var
import Core.Syntax
import Support.UniqMap
import Support.Unique
import Typing.Type

import Control.Arrow
import Control.Lens
import Control.Monad.RWS
import Data.Foldable
import Data.Graph
import qualified Data.Text as T

-- Lambdas that have been lifted to top-level functions.
type GenFuncs = Endo [CoreTopFunction]

type VarSet = UniqMap Var

data LLOut = LLOut
  { _genFuncs  :: GenFuncs
  , _boundVars :: VarSet
  , _freeVars  :: VarSet
  , _types     :: [Type TyVar]
  }

makeLenses ''LLOut

instance Semigroup LLOut where
  LLOut x y z w <> LLOut x' y' z' w' =
    LLOut (x <> x') (y <> y') (z <> z') (w <> w')

instance Monoid LLOut where
  mempty = LLOut mempty mempty mempty mempty

-- Monad for lambda lifting code transformation
type LLM a = RWS VarSet LLOut Unique a

-- Globals are visible from any scope.
-- They are never considered to be free variables.
llGlobals :: LLM VarSet
llGlobals = ask

diffFv :: [Var] -> LLM a -> LLM a
diffFv [] = id
diffFv [x] = censor (freeVars %~ deleteUM x)
diffFv xs = censor (freeVars %~ (`diffUM` fromListUM' xs))

uniqVar :: Var -> LLM Var
uniqVar x = do
  uniq <- get
  put $! nextUnique uniq
  return $! x & nameLens.uniqLens .~ uniq

uniqFuncVar :: TypeScheme TyVar -> LLM Var
uniqFuncVar ty = do
  uniq <- get
  put $! nextUnique uniq
  let name = mkName (T.pack "lam") uniq NoLocation
  let var = mkId name Immutable ty
  return var

toUniqMapOf :: Uniquable a => Getting (UniqMap a) s a -> s -> UniqMap a
toUniqMapOf f = foldMapOf f singletonUM'

-- Traverse type variables in the type of the (regular) variable.
traverseTyVarInVar :: Traversal' Var TyVar
traverseTyVarInVar = typesInVar.traverse

letReturnType :: CoreLet -> Type TyVar
letReturnType (CoreLet _ xs) = case xs of
  [] -> mkTypeUnit
  [x] -> _typeSchemeType $ idType x
  xs -> mkTypeTuple $ map (_typeSchemeType.idType) xs

llFreeVars :: VarSet -> LLM ()
llFreeVars vars = do
  globs <- llGlobals
  freeVars `scribe` (filterUM (not . isBuiltinVar) vars `diffUM` globs)

freeVarsInCoreLetLLM :: CoreLet -> LLM (UniqMap Var)
freeVarsInCoreLetLLM lt = do
  (_lt', LLOut _ _bvs fvs _ts) <- listen $ llLet lt
  return fvs

freeVarsInCoreLet :: Unique -> CoreLet -> UniqMap Var
freeVarsInCoreLet u lt = case runRWS (freeVarsInCoreLetLLM lt) emptyUM u of (res, _, _) -> res

llExpr :: CoreExpr -> LLM CoreExpr
llExpr (CeLam is xs lt) = do
  (lt', LLOut _ bvs fvs ts) <- listen $ diffFv xs $ llLet lt
  -- Unfortunately we can't only rely on ts containing relevant type variables.
  -- We also have to get types that all variables (free or bound) have.
  -- TODO: Are all these guaranteed to be identifiers?
  let xsSet = fromListUM' xs
  let allVars = xsSet <> bvs <> fvs
  let tvsInVars = unionsUM $ fmap (fvTypeScheme.idType) allVars
  let tvsInTypes = toUniqMapOf (traverse.traverse) ts
  let tyvars = tvsInVars <> tvsInTypes
  tyVarSubst <- mapM uniqVar tyvars
  let rnTyVar x = findWithDefaultUM x x tyVarSubst
  -- Rename types in all variables
  let vs' = allVars & traverse.traverseTyVarInVar %~ rnTyVar
  varSubs <- mapM uniqVar vs'
  let rnVar x = findWithDefaultUM x x varSubs
  -- Construct a new function:
  let funBody = lt' & traverse %~ rnVar & traverse %~ rnTyVar
  let funArgs = (toList fvs ++ xs) & traverse %~ rnVar
  let funTyArgs = tyvars & traverse %~ rnTyVar
  let funTy = mkFunArgs (map (_typeSchemeType.idType) funArgs) (letReturnType funBody)
  let funScheme = mkScheme (toList funTyArgs) [] funTy
  funVar <- uniqFuncVar funScheme
  let mkLamParam = SimpleFuncParam PassByValue
  let fun = CoreTopFunction funVar (map mkLamParam funArgs) funBody is IsLambda
  genFuncs `scribe` Endo (fun :)
  -- Construct call:
  let callTyParams = [mkTVar v (tyVarKind v) | v <- toList tyvars]
  types `scribe` callTyParams
  return $ CeCall NotVectorized funVar callTyParams (toList fvs) NoLocation
llExpr e = do
  llFreeVars $ toUniqMapOf varsInCoreExpr e
  types `scribe` toListOf typeInCoreExpr e
  letInCoreExpr llLet e

llLet :: CoreLet  -> LLM CoreLet
llLet lt@(CoreLet bs _) = do
  let defs = concat [xs | CoreBind _ (CorePat xs) _ <- bs]
  boundVars `scribe` fromListUM' defs
  diffFv defs $ exprInCoreLet llExpr lt

llTopFunc :: CoreTopFunction -> LLM CoreTopFunction
llTopFunc (CoreTopFunction f xs lt is il) = (\ lt -> CoreTopFunction f xs lt is il) <$> llLet lt

llGetLiftedFuncs :: LLM a -> LLM (a, [CoreTopFunction])
llGetLiftedFuncs act = censor (genFuncs .~ mempty) $
  second (`appEndo` []) <$> listens _genFuncs act

llProg :: CoreProgram -> LLM CoreProgram
llProg (CoreProgram es fs impls) = do
  lams <- forM fs $ \case
    AcyclicSCC f -> do
      (f', fLams) <- llGetLiftedFuncs $ llTopFunc f
      return $ map AcyclicSCC fLams ++ [AcyclicSCC f']
    CyclicSCC fs -> do
      -- TODO: All functions returned in this acyclic block might not actually be acyclic.
      -- Should we apply a pass here to return them in a proper order?
      (fs', fsLams) <- llGetLiftedFuncs $ mapM llTopFunc fs
      return [CyclicSCC (fsLams ++ fs')]
  implLams <- forM impls $ \ (CoreStructImpl t fs) -> do
      (fs', fsLams) <- llGetLiftedFuncs $ mapM llTopFunc fs
      return (CoreStructImpl t (fsLams ++ fs'))
  return $ CoreProgram es (concat lams) implLams

coreLambdaLift :: Unique -> CoreProgram -> (CoreProgram, Unique)
coreLambdaLift u prog@CoreProgram{..} = case runRWS (llProg prog) globs u of
  (x, u, _) -> (x, u)
  where
    globs = toUniqMapOf (traverse.traverse.to _coreFunName) _coreFunctions
