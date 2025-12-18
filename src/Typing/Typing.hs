{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
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

module Typing.Typing (
  TypedProgram(..),
  TypedTopConstant(..),
  TypedTopExtern(..),
  TypedTopFunction(..),
  TypedStructImpl(..),
  TypedDefault(..),
  tcModules,
  findFunType
) where

import Basic.Location
import Basic.Name
import Basic.Var
import Parser.Effect
import Parser.Syntax
import Support.Pretty
import Support.UniqMap
import Typing.ConstraintSolver
import Typing.Kind (mkKfun)
import Typing.StructEnv
import Typing.TcM
import Typing.KindChecker

import Control.Arrow (first)
import Control.Lens.Combinators (Traversal', toListOf)
import Control.Lens.Operators ((%~), (&), (.~), (^.), (%%~))
import Control.Lens.Plated
import Control.Lens.TH (makeLensesFor)
import Control.Monad.Cont
import Data.Either (rights, fromRight)
import Data.Function (on)
import Data.Graph (graphFromEdges, Tree(..), transposeG, dfs, SCC (..), stronglyConnComp, stronglyConnCompR, flattenSCCs)
import Data.List (sortOn, partition, union, groupBy)
import Data.Maybe
import GHC.Natural (naturalToInteger)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Foldable (traverse_)


{------------------------
 -- Type check program --
 ------------------------}

data TypedTopConstant = TypedTopConstant
  { _tConstName :: Id
  , _tConstBody :: Expr Var
  }

data TypedTopExtern = TypedTopExtern
  { _tExtName     :: Id
  , _tExtIsPublic :: Bool
  , _tExtArgs     :: [SimpleFuncParam Id]
  , _tExtEff      :: Maybe (Located (PolymorphicTypeWithEffect Var))
  }

data TypedTopFunction = TypedTopFunction
  { _tFunName     :: Id
  , _tFunIsPublic :: Bool
  , _tFunArgs     :: [SimpleFuncParam Id]
  , _tFunBody     :: Expr Var
  , _tFunEff      :: Maybe (Located (PolymorphicTypeWithEffect Var))
  , _tFunIsSieve  :: IsSieveFn
  }

data TypedStructImpl = TypedStructImpl
  { _tImplType :: Type Var
  , _tImplMethods :: [TypedTopFunction]
  }

newtype TypedDefault = TypedDefault
  { _tDefaultFields :: [Located Integer]
  }

makeLensesFor [("_tExtName", "tExtName")] ''TypedTopExtern
makeLensesFor [("_tFunName", "tFunName"), ("_tFunBody", "tFunBody")] ''TypedTopFunction
makeLensesFor [("_tImplMethods", "tImplMethods")] ''TypedStructImpl

findNaturalAsInteger
  :: Type Var -> TcM (Located Integer)
findNaturalAsInteger t@ (TNat n)
  = case n of
      Finite i
        -> return (Located (location t) (toInteger i))
      _ -> tcSetLoc (location t) $ tcThrowErr "Infinity found where field was expected"
findNaturalAsInteger t@ (TVar _ _ _)
  = tcSetLoc (location t) $ tcThrowErr "Undefined type variable"
findNaturalAsInteger t
  = tcSetLoc (location t) $ tcICE "Non-natural type used as natural type"

traverseVarInTypedTopFunction :: Traversal' TypedTopFunction Var
traverseVarInTypedTopFunction f TypedTopFunction{..} =
  TypedTopFunction <$> f _tFunName <*> pure _tFunIsPublic <*> traverse (traverse f) _tFunArgs <*> traverse f _tFunBody <*> pure _tFunEff <*> pure _tFunIsSieve

traverseVarInTypedTopExtern :: Traversal' TypedTopExtern Var
traverseVarInTypedTopExtern f TypedTopExtern{..} =
  TypedTopExtern <$> f _tExtName <*> pure _tExtIsPublic <*> traverse (traverse f) _tExtArgs <*> pure _tExtEff

simpTypesInExpr :: Expr Var -> Expr Var
simpTypesInExpr = traverseTypeInExpr %~ simpType

simpTypesInTypedTopFunction :: TypedTopFunction -> TypedTopFunction
simpTypesInTypedTopFunction = tFunBody %~ simpTypesInExpr

traverseTypedTopFunctionInTypedStructImpl :: Traversal' TypedStructImpl TypedTopFunction
traverseTypedTopFunctionInTypedStructImpl f = tImplMethods . traverse %%~ f

data TypedProgram = TypedProgram
  { _tProgExterns :: [TypedTopExtern]
  , _tProgFunctions :: [SCC TypedTopFunction]
  , _tProgStructImpls :: [TypedStructImpl]
  , _tProgImports :: [LImport]
  , _tProgDefaults :: TypedDefault
  , _tVars :: [(Name, Var)]
  }

simpTypesInTypedProgram :: TypedProgram -> TypedProgram
simpTypesInTypedProgram TypedProgram{..} = TypedProgram
  { _tProgExterns = _tProgExterns
  , _tProgFunctions = (map . fmap) simpTypesInTypedTopFunction _tProgFunctions
  , _tProgStructImpls = map (traverseTypedTopFunctionInTypedStructImpl %~ simpTypesInTypedTopFunction) _tProgStructImpls
  , _tProgImports = _tProgImports
  , _tProgDefaults = _tProgDefaults
  , _tVars = _tVars
  }

sccTypedTopFuncs :: [TypedTopFunction] -> [SCC TypedTopFunction]
sccTypedTopFuncs fs = stronglyConnComp (map mkNode fs)
  where
    allKeys = map _tFunName fs
    mkNode f = let
        k = _tFunName f
        vars = occurVars $ _tFunBody f
        ks = [k' | k' <- allKeys, k' `memberUM` vars]
      in (f, k, ks)

-- The first list is supposed to contain global functions, other lists are supposed to contain functions in struct impls
sccFuncs :: [[Function Name]] -> [SCC (Function Name, Name, [Name])]
sccFuncs (fs : ifss)
  = stronglyConnCompR (fmap mkTopNode (zip fs allTopKeys) ++ fmap mkImplNode (zip ifs allImplKeys))
  where
    funName = unLocated . _sigName . unLocated . _funSignature
    funVars = occurVars . _funBody
    ifs = concat ifss
    allTopKeys = fmap funName fs
    allImplKeys = fmap funName ifs
    allKeys = allTopKeys ++ allImplKeys
    dependings fun = filter (`memberUM` funVars fun) allKeys
    finalizers = filter ((== "finalize") . nameOccName) allImplKeys
    -- Top level functions are approximated to potentially call all finalizers
    mkTopNode (fun, name) = (fun, name, dependings fun ++ finalizers)
    mkImplNode (fun, name) = (fun, name, dependings fun)
sccFuncs _
  = error "Panic! - sccFuncs [] should be unreachable."

preorder
  :: Tree a -> [a]
preorder t
  = let
      preorder (Node x ts) acc
        = x : foldr preorder acc ts
    in
    preorder t []

hypertoporder
  :: SCC (Function Name, Name, [Name]) -> [Function Name]
hypertoporder (AcyclicSCC (fun, _, _))
  = [fun]
hypertoporder (CyclicSCC ts@ ((_, name, _) : _))
  = let
      (graph, deindex, index) = graphFromEdges ts
      central = fromJust (index name)
      half1 = reverse . tail . preorder . head . dfs graph . return $ central
      half2 = tail . preorder . head . dfs (transposeG graph) . return $ central
    in
    fmap ((\ (x, _, _) -> x) . deindex) (half1 ++ [central] ++ half2)
hypertoporder (CyclicSCC _)
  = error "Panic! - hypertoporder (CyclicSCC []) should be unreachable."

-- Moves unsolved predicates that are allowed to be implicit (undeclared in signature) to the signature
implicitPredicatesAsGiven
  :: (TypedTopFunction, TypePreds) -> (TypedTopFunction, TypePreds)
implicitPredicatesAsGiven (ttf, tps)
  = let
      (gs, tpsrest)
        = partition isPredAllowedImplicitly tps
    in
    (ttf & tFunName . typeLens . typeSchemePredicates %~ (`union` gs) , tpsrest)

findFinalizer :: StructImpl Name -> Maybe Name
findFinalizer impl
  = listToMaybe $
    filter ((== "finalize") . nameOccName) $ 
    fmap (unLocated . _sigName . unLocated . _funSignature . unLocated) $ 
    _structImplBody impl

implStruct :: StructImpl name -> TcM name
implStruct impl
  = case _structImplType impl of
      TVar name            _ _ -> return name
      TApp (TVar name _ _) _ _ -> return name
      _                        -> tcFatal "Impl block must associate to a struct"

finalizers :: [StructImpl Name] -> TcM (UniqMap Name)
finalizers impls
  = do
      pairs <- forM impls $ \ impl -> do
        name <- implStruct impl
        return (name , findFinalizer impl)
      return (mapMaybeUM id (fromListUM pairs))

orderTypes :: Program Name -> TcM [Either (LTypeDef Name) (LStructDecl Name)]
orderTypes Program{..} = tcThrowIfErrs $ do
  maybeComps <- forM components $ \case
    AcyclicSCC typedef -> return (Just typedef)
    CyclicSCC subcomps -> do
      let nodeName node = unLocated (case node of
            Left (Located _ tyDef) -> _tyDefName tyDef
            Right (Located _ structDecl) -> _structDeclName structDecl)
      forM_ subcomps $ \node -> tcSetLoc (location node) $ do
        let name = pprintName (nodeName node)
        tcAddErr $ "Type synonym" <+> name <+> "defined recursively."
      return Nothing
  return $ catMaybes maybeComps
  where
    ul = unLocated
    allNames = fromListUM' $
      map (ul._tyDefName.ul) _programTypeDefs ++
      map (ul._structDeclName.ul) _programStructDecls
    mkNode var item vars = (item, var, elemsUM $ allNames `intersectUM` vars)
    getVarBounds = fromListUM' . map ul . concatMap getTyParamNames
    defNodes = [mkNode name (Left tdef) vars |
      tdef <- _programTypeDefs,
      let name = ul $ _tyDefName $ ul tdef,
      let varsInDef = fvType $ _tyDefType $ ul tdef,
      let varsBound = getVarBounds $ ul $ _tyDefParams $ ul tdef,
      let vars = varsInDef `diffUM` varsBound]
    structNodes = [mkNode name (Right sdecl) vars |
      sdecl <- _programStructDecls,
      let name = ul $ _structDeclName $ ul sdecl,
      let varsInBody = unionsUM $ map (fvType._fieldDeclType) $ _structDeclFields $ ul sdecl,
      let varsBound = getVarBounds $ _structDeclTypeParams $ ul sdecl,
      let vars = varsInBody `diffUM` varsBound]
    components = stronglyConnComp $ defNodes ++ structNodes

tcTypeDefParam :: TypeParam Name -> ContT a TcM [TyVar]
tcTypeDefParam param = case param of
  TypeParam x k -> return <$> go x k
  TypeParamQualify t ms d -> do
    v1 <- go t KindUnqualified
    mv2 <- traverse (`go` KindStage) ms
    v3 <- go d KindDomain
    return $ [v1] ++ maybeToList mv2 ++ [v3]
  where
    go (Located l name) k = ContT $ \cont ->
      let v = mkTyVar name k in
        tcSetLoc l $ tcSetVar name v (cont v)

tcTypeDefParams :: [TypeParam Name] -> ([TyVar] -> TcM a) -> TcM a
tcTypeDefParams params = runContT (concat <$> mapM tcTypeDefParam params)

tcTypeDef :: TypeDef Name -> TcM a -> TcM a
tcTypeDef TypeDef{..} act = do
  let name = unLocated _tyDefName
  let resKind = unLocated _tyDefResultKind
  unless (null $ unLocated _tyDefConstraints) $
    tcThrowErr "Constrained type synonyms currently not supported."
  tcTypeDefParams (unLocated _tyDefParams) $ \vars -> do
    tcSetVarSet (fromListUM' vars) $ do
      definedType <- tcCheckTypeKind' resKind _tyDefType
      let missingStageLocs = missingStages definedType
      unless (null missingStageLocs) $
        tcThrowErr $
          "Implicit stage must not occur in type synonym." $$
          "Either define an unqualified type or make the type synonym stage polymorphic."
      let scheme = mkScheme vars [] definedType
      let argsKs = map tyVarKind vars
      tcSetType name (mkKfun argsKs resKind) scheme act

missingStages :: Type a -> [Location]
missingStages = go NoLocation
  where
    go l t = case t of
      TCon ConNoStage _ -> [l']
      _ -> concatMap (go l') (children t)
      where l' = if hasLocation t then location t else l

tcStructDecl :: UniqMap Name -> StructDecl Name -> TcM a -> TcM a
tcStructDecl finmap StructDecl{..} act = do
  let tyVarList = concatMap typeParamNameToVar _structDeclTypeParams
  l <- tcGetLoc
  let k = mkKfun (map tyVarKind tyVarList) KindUnqualified
  let structName = unLocated _structDeclName
  let structVar = mkTyVar structName k
  let structTy = TVar structVar k l
  let structTyScheme = TForAll tyVarList [] structTy
  structFields <- tcThrowIfErrs $
    tcSetVarSet (fromListUM' tyVarList) $ do
      forM _structDeclFields $ \(StructFieldDecl fieldName fieldType) -> do
        fieldType' <- tcTypeNoReplaceMissingStages KindStar fieldType
        forM_ (missingStages fieldType') $ \l ->
          tcSetLoc l $ tcAddErr "Missing stage in struct."
        return (unLocated fieldName, fieldType')
  tcSetStruct structName structFields structTyScheme (lookupUM structName finmap)
  tcSetVar structName structVar act

tcTypeDecls :: UniqMap Name -> [Either (LTypeDef Name) (LStructDecl Name)] -> TcM a -> TcM a
tcTypeDecls finmap = foldr ((.) . step) id
  where
    step (Left (Located l tdef)) = tcSetLoc l . tcTypeDef tdef
    step (Right (Located l sdecl)) = tcSetLoc l . tcStructDecl finmap sdecl

tcDefaults :: LDefault Name -> TcM TypedDefault
tcDefaults defaults
  = do
      typedDefaultFields <- traverse (tcType KindNat) . _defaultFields . unLocated $ defaults
      TypedDefault <$> traverse findNaturalAsInteger typedDefaultFields

tcProgram :: Program Name -> (TypedProgram -> TcM a) -> TcM a
tcProgram prog@(Program _ _ fs es imports impls defaults) cont = do
  let ulimpls = fmap unLocated impls
  decls <- orderTypes prog
  finmap <- finalizers ulimpls
  tcTypeDecls finmap decls $ do
    defaults' <- tcDefaults defaults
    exts <- tcThrowIfErrs $ forM es $ tcWithLoc $ \ sign -> do
              loc <- tcGetLoc
              let lsign = Located loc sign
              (freeVars, var) <- tcWithLoc tcSignScheme lsign
              let pss = map _fnParamStyle . unLocated . _sigParameters $ sign
              return (freeVars, var, lsign, pss)
    funcss <- tcThrowIfErrs $
      forM (fs : fmap _structImplBody ulimpls) $ \funcs -> forM funcs $ tcWithLoc $ \func -> do
        let sign = _funSignature func
        (freeVars, var) <- tcWithLoc tcSignScheme sign
        let pss = map _fnParamStyle . unLocated . _sigParameters $ unLocated sign
        loc <- tcGetLoc
        return (freeVars, var, Located loc func, pss)
    let globs = fmap (\ (_, var, _, _) -> (varName var, var)) exts : fmap (fmap (\ (_, var, _, _) -> (varName var, var))) funcss
    let params = fmap (\ (_, var, _, params) -> (var, params)) exts : fmap (fmap (\ (_, var, _, params) -> (var, params))) funcss
    let levs = fmap (\ (fvs, _, le, _) -> (fvs, le)) exts
    let lfvs = fmap (fmap (\ (fvs, _, lf, _) -> (fvs, lf))) funcss
    tcSetVars (concat globs) $ 
      tcSetTopFunParams (concat params) $ do
        (exts', env1) <- tcThrowIfErrs $ tcExterns levs
        (funcss', env2) <- tcThrowIfErrs $ updEnv (tcTyEnv .~ _tcTyEnv env1) $ tcFunctions lfvs
        let (exts'', cs) = unzip $ exts'
        let (funcss'', css) = unzip $ fmap unzip $ funcss'
        tcThrowIfErrs $ tcCheckConstr (concat (cs ++ concat css))
        let forM2 a b op = zipWithM op a b
        impls' <- forM2 ulimpls (tail funcss'') $ \ impl funcs'' -> do
          t <- tcType KindUnqualified (_structImplType impl)
          return $ TypedStructImpl { _tImplType = t, _tImplMethods = funcs'' } 
        let fieldsUsedByFunMatchess = fmap fieldsUsedByFun (head funcss'')
        let fieldsUsedByImplMatchess = fmap fieldsUsedByFun (concatMap _tImplMethods impls')
        let badMatches = filter ((> 1) . length . snd) (concat (fieldsUsedByFunMatchess ++ fieldsUsedByImplMatchess))
        let res = TypedProgram
                  { _tProgExterns = exts''
                  , _tProgFunctions = sccTypedTopFuncs (head funcss'')
                  , _tProgStructImpls = impls'
                  , _tProgImports = imports
                  , _tProgDefaults = defaults'
                  , _tVars = concat (take 2 globs)
                  }
        if null badMatches
          then return ()
          else tcThrowIfErrs $ traverse_ (\ (loc , _) -> tcSetLoc loc (tcAddErr "Cases of match expression use multiple fields")) badMatches
        updEnv (tcTyEnv .~ _tcTyEnv env2) $ cont res

-- | Type check modules. Expects topologically sorted modules and returns them in the same order.
tcModules :: [Module (LProgram Name)]  -> TcM [Module TypedProgram]
tcModules mods = runContT (mapM (ContT . go) mods) return
  where
    -- NOTE: we are type type checking all modules as if they were concatenated
    -- one after another. Renamer already resolved imports and exports properly.
    -- Identical names defined in different modules will get different unique
    -- identifiers.
    go (Located l prog, name, imports) cont =
      tcSetLoc l $ tcProgram prog $ \prog' ->
        cont (simpTypesInTypedProgram prog', name, imports)

{-------------------------
 -- Type check function --
 -------------------------}

type TyVarSet = UniqMap Var

tcSignScheme :: Signature Name -> TcM (TyVarSet, Id)
tcSignScheme sign = do
  let tyargs =
        fromListUM $
        map (\var -> (varName var, var)) $
        concatMap typeParamNameToVar
        (unLocated (_sigTypeParameters sign))
  tcSetVarSet tyargs $ do
    cs <- tcWithLoc tcConstraint (_sigConstraints sign)
    args <- tcWithLoc (mapM (tcType' KindStar . _fnParamType)) (_sigParameters sign)
    ret <- tcType' KindStar (_sigReturnType sign)
    let
      args' | null args = [mkTypeUnit]
            | otherwise = args
      funType = mkFunArgs args' ret
      signType = TForAll (elemsUM tyargs) cs funType
      identif = mkId (unLocated $ _sigName sign) Immutable signType
    return (tyargs, identif)
  where
    tcType' = tcTypeNoReplaceMissingStages

typeParamNameToVar :: TypeParam Name -> [Var]
typeParamNameToVar (TypeParam n k) = [mkTyVar (unLocated n) k]
typeParamNameToVar (TypeParamQualify ty mStage dom) = [vty] ++ vStage ++ [vdom]
  where
    vty = mkTyVar (unLocated ty) KindUnqualified
    vdom = mkTyVar (unLocated dom) KindDomain
    vStage = [mkTyVar (unLocated stage) KindStage | Just stage <- [mStage]]

-- TODO: currently the generated non-meta variables are named using
-- tcFreshUniq. Since they are local to the function, it would be nicer to name
-- them s1, s2 and so on. To avoid collisions, that would require looking up
-- variables by occ names instead of integers.
stageMetaToVar :: UniqMap Var -> Located Var -> TcM (UniqMap Var)
stageMetaToVar subs (Located loc var)
  | isMetaTyVar var && tyVarKind var == KindStage = do
      uniq <- tcFreshUniq
      let name = mkName ("s_" <> T.pack (show uniq)) uniq loc
      let var' = mkTyVar name KindStage
      return $ insertUM var var' subs
  | otherwise = return subs

replaceStageQuantifiersInVar
  :: Var -> UniqMap Var -> Var
replaceStageQuantifiersInVar var sigStageVars
  = mkId (varName var) Immutable $
    idType var & typeSchemeQuantifiers %~ (++ elemsUM sigStageVars)

replaceStageQuantifiersInTypedTopFunction :: TypedTopFunction -> UniqMap Var -> TypedTopFunction
replaceStageQuantifiersInTypedTopFunction funcDecl sigStageVars =
  funcDecl & tFunName .~ var'
  where
    var = funcDecl ^. tFunName
    var' = replaceStageQuantifiersInVar var sigStageVars

replaceStageQuantifiersInTypedTopExtern :: TypedTopExtern -> UniqMap Var -> TypedTopExtern
replaceStageQuantifiersInTypedTopExtern extDecl sigStageVars =
  extDecl & tExtName .~ var'
  where
    var = extDecl ^. tExtName
    var' = replaceStageQuantifiersInVar var sigStageVars

tcEffect :: Effect' Name Name -> TcM (Effect' Var Var)
tcEffect (Effect [] ts) = Effect [] . map snd <$> mapM tcInferTypeKind ts
tcEffect _ = tcICE "tcEffect: _effectMetaVars must be empty for effect annotations"

tcTypeWithEffect :: TypeWithEffect' Name Name -> TcM (TypeWithEffect' Var Var)
tcTypeWithEffect TweAny = return TweAny
tcTypeWithEffect (TweTuple twes) = TweTuple <$> mapM tcTypeWithEffect twes
tcTypeWithEffect (TweFun twe1 twe2 e []) = TweFun <$> tcTypeWithEffect twe1 <*> tcTypeWithEffect twe2 <*> tcEffect e <*> pure []
tcTypeWithEffect TweFun{} = tcThrowErr "Constraints not yet supported in effect annotations"

tcPolymorphicTypeWithEffect :: PolymorphicTypeWithEffect Name -> TcM (PolymorphicTypeWithEffect Var)
tcPolymorphicTypeWithEffect (PolyTwe es twe) = do
  let es' = map (flip mkTyVar KindEffect) es
  tcSetVars (zip es es') $ PolyTwe es' <$> tcTypeWithEffect twe

tcSignature
  :: TyVarSet -> Signature Name -> 
     (Id -> [SimpleFuncParam Id] -> Maybe (Located (PolymorphicTypeWithEffect Var)) -> Type Var -> Type Var -> [TypePred Var] -> TcM a) ->
     TcM a
tcSignature freeVars sign cont = tcSetVarSet freeVars $ do
  let name = _sigName sign
  tcDebugPrint $ "***** Function:" <+> pprintName (unLocated name)
  originalVar <- tcWithLoc findId name

  -- Replace ConNoStage with meta type variables in the signature
  let originalScheme = idType originalVar
  ty <- tcNoStageToMetaVar (originalScheme ^. typeSchemeType)
  let polymorphicScheme = originalScheme & typeSchemeType .~ ty
  let var = mkId (varName originalVar) Immutable polymorphicScheme

  let arity = signatureArity sign
  (argTys, retTy) <- tcTypeSplitFunc ty $
    if arity == 0 then 1 else arity
  let
    nameParams = [SimpleFuncParam pt n | (pt, Located _ n, _) <- signParams $ sign]
    passingStyleToMut = \case
      PassByValue -> Immutable
      PassByRef -> Mutable
    paramNameToVar (SimpleFuncParam pt n) t =
      case n of
        Nothing -> error "TODO: self not implemented."
        Just n -> SimpleFuncParam pt (mkId n (passingStyleToMut pt) (typeToScheme t))
    varParams = zipWith paramNameToVar nameParams argTys
  eff <- case _sigEffect $ sign of
           Nothing -> return Nothing
           Just (Located loc e) -> Just . Located loc <$> tcPolymorphicTypeWithEffect e

  -- TODO: I think we should also verify givens in some way?
  let TForAll _ givens _ = polymorphicScheme
  cont var varParams eff retTy ty givens

tcExtern :: TyVarSet -> Signature Name -> TcM (TypedTopExtern, TypePreds)
tcExtern freeVars sign = 
  tcSignature freeVars sign $ \ var varParams eff retTy ty givens -> do
    let um = fromListUM [(varName v, v) | SimpleFuncParam _ v <- varParams]
    tcSetReturnType retTy $
      tcSetVarSet um $ do

        -- After solving the constraints we will check if there are stage meta
        -- variables in the signature. If there are, the function is stage
        -- polymorphic and each such stage meta variable is replaced with a type
        -- variable.
        (wc, subs, unsolvedStageVars) <- tcSimplifyConstraints givens
  
        sigStageVars <- foldM stageMetaToVar emptyUM $
                        typeGetVarsWithLoc $ subType subs ty
  
        forM_ (unsolvedStageVars `diffUM` sigStageVars)
          tcReportUnsolved
  
        -- annoyingly, we have to manually substitute all types and all variables
        -- in the function
        let sigStageSubs = flip mapUM sigStageVars $ \var ->
              TVar var KindStage (location var)
        let subs' = mapUM (subType sigStageSubs) subs
        let f = subType (sigStageSubs `unionUM` subs')

        let extDecl = TypedTopExtern var (_sigIsPublic sign) varParams eff
        let extDecl' = extDecl & traverseVarInTypedTopExtern . typesInVar %~ f
        let extDecl'' = replaceStageQuantifiersInTypedTopExtern extDecl' sigStageVars
        return $ (extDecl'', wc)

tcExterns
  :: [(TyVarSet, Located (Signature Name))] -> TcM ([(TypedTopExtern, TypePreds)] , Env)
tcExterns exts
  = let
      extName
        = unLocated . _sigName
      varsetmap
        = fromListUM . fmap (\ (set , lext) -> (extName . unLocated $ lext , (location lext , set))) $ exts
      
      go (ext : exts) results
        = do
            let name = extName ext
            let (loc , varset) = findUM name varsetmap
            result <- tcTry $ tcWithLoc (tcExtern varset) (Located loc ext)
            let cont = go exts (result : results)
            case result of
              Left _
                -> cont
              Right (extDecl , _)
                -> do
                     -- Overwrite function Id in the environment in case the signature was changed after type inference
                     let var = extDecl ^. tExtName
                     tcSetVar name var $ cont
      go _            results
        = do
            env <- getEnv
            return (reverse results , env)
    in
    do
      (results , env) <- go (fmap (unLocated . snd) exts) []
      return (rights results , env)

tcFunction :: TyVarSet -> Function Name -> TcM (TypedTopFunction, TypePreds)
tcFunction freeVars func = 
  let sign = unLocated $ _funSignature func in
  tcSignature freeVars sign $ \ var varParams eff retTy ty givens -> do
    let um = fromListUM [(varName v, v) | SimpleFuncParam _ v <- varParams]
    tcSetReturnType retTy $
      tcSetVarSet um $ do
        body <- tcExprA retTy (_funBody func)

        -- After solving the constraints we will check if there are stage meta
        -- variables in the signature. If there are, the function is stage
        -- polymorphic and each such stage meta variable is replaced with a type
        -- variable.
        (wc, subs, unsolvedStageVars) <- tcSimplifyConstraints givens
  
        sigStageVars <- foldM stageMetaToVar emptyUM $
                        typeGetVarsWithLoc $ subType subs ty
  
        forM_ (unsolvedStageVars `diffUM` sigStageVars)
          tcReportUnsolved
  
        -- annoyingly, we have to manually substitute all types and all variables
        -- in the function
        let sigStageSubs = flip mapUM sigStageVars $ \var ->
              TVar var KindStage (location var)
        let subs' = mapUM (subType sigStageSubs) subs
        let f = subType (sigStageSubs `unionUM` subs')
        let body' = body & traverseTypeInExpr %~ f
        let funcDecl = TypedTopFunction var (_sigIsPublic sign) varParams body' eff (_funIsSieve func)
        let funcDecl' = funcDecl & traverseVarInTypedTopFunction.typesInVar %~ f
        let funcDecl'' = replaceStageQuantifiersInTypedTopFunction funcDecl' sigStageVars
        return $ implicitPredicatesAsGiven (funcDecl'', wc)

tcFunctions
  :: [[(TyVarSet, Located (Function Name))]] -> TcM ([[(TypedTopFunction, TypePreds)]] , Env)
tcFunctions funcss
  = let
      funName
        = unLocated . _sigName . unLocated . _funSignature
      varsetmap
        = fromListUM . fmap (\ (set , lfun) -> (funName . unLocated $ lfun , (location lfun , set))) . concat $ funcss
      
      go (func : funcs) results
        = do
            let name = funName func
            let (loc , varset) = findUM name varsetmap
            result <- tcTry $ tcWithLoc (tcFunction varset) (Located loc func)
            let cont = go funcs (result : results)
            case result of
              Left _              
                -> cont
              Right (funcDecl , _) 
                -> do
                     -- Overwrite function Id in the environment in case the signature was changed after type inference
                     let var = funcDecl ^. tFunName
                     tcSetVar name var $ cont
      go _              results
        = do
            env <- getEnv
            return (reverse results , env)
      
      restoreOrder resultmap
        = fmap (mapMaybe (\ (_ , func) -> lookupUM (funName . unLocated $ func) resultmap)) funcss
    in
    do
      (results , env) <- go (concatMap hypertoporder . sccFuncs . fmap (fmap (unLocated . snd)) $ funcss) []
      let resultmap = fromListUM (fmap (\ (res , preds) -> (varName . _tFunName $ res , (res , preds))) . rights $ results)
      return (restoreOrder resultmap , env)

tcTypeSplitFunc :: Type a -> Int -> TcM ([Type a], Type a)
tcTypeSplitFunc _  n | n < 0 = tcICE "Negative split position."
tcTypeSplitFunc ty 0 = return ([], ty)
tcTypeSplitFunc ty n = case ty of
  TQualify (TFun t1 t2) _ _ -> first (t1 :) <$> tcTypeSplitFunc t2 (n - 1)
  TFun t1 t2 -> first (t1 :) <$> tcTypeSplitFunc t2 (n - 1)
  _ -> tcICE "Expecting more function arguments."

signatureArity :: Signature a -> Int
signatureArity = length . unLocated . _sigParameters

{-----------------
 -- Check types --
 -----------------}

instantiateType :: TypeScheme Var -> TcM ([TypePred TyVar], Type TyVar, [TyVar])
instantiateType (TForAll vars preds ty) = do
  (sub, vs') <- tcSubFresh vars
  let preds' = map (subTypePred sub) preds
  return (preds', subType sub ty, vs')

tcSubFresh :: [Var] -> TcM (UniqMap (Type Var), [TyVar])
tcSubFresh vs = first fromListUM . unzip <$> mapM doVar vs
  where
    doVar v = do
      let k = tyVarKind v
      metaVar <- tcFreshMetaTyVar k
      t <- TVar (setLocation metaVar (location v)) k <$> tcGetLoc
      return ((v, t), metaVar)

tcTypeArgument :: Maybe (TypeArgument Name) -> TyVar -> TcM (TypeArgument TyVar)
tcTypeArgument Nothing x = TypeArg . TVar x (tyVarKind x) <$> tcGetLoc
tcTypeArgument (Just (TypeArg t)) x = do
  let k = tyVarKind x
  t1 <- tcCheckTypeKind' k t
  t2 <- TVar x k <$> tcGetLoc
  tcUnifyTypes t1 t2
  return $ TypeArg t1
tcTypeArgument (Just _) _ = tcFatal "Named type arguments not yet supported."

tcTypeArguments :: [TypeArgument Name] -> [TyVar] -> TcM [TypeArgument TyVar]
tcTypeArguments args metaVars = do
  unless (length args <= length metaVars) $
    tcThrowErr "Too many type arguments."
  zipWithM tcTypeArgument (map Just args ++ repeat Nothing) metaVars

{----------------------------------
 -- Type checking of expressions --
 ----------------------------------}

-- Assumes that type inference has annotated all expressions with types already
getExprType :: Expr Var -> Type TyVar
getExprType (Ascription _ t) = t
getExprType (TypeAnnot t _)  = t
getExprType (ExprLoc _ e)    = getExprType e
getExprType _                = error "getExprType: Unreachable"

tcExprA :: QualifiedType Var -> Expr Name -> TcM (Expr Var)
tcExprA resTy e = TypeAnnot resTy <$> tcExpr resTy e

tcExpr :: QualifiedType Var -> Expr Name -> TcM (Expr Var)
tcExpr resTy (Ascription e ty) = do
  ty' <- tcType KindStar ty
  e' <- tcExpr ty' e
  tcUnifyTypes resTy ty'
  return $ Ascription e' ty'

tcExpr resTy (Assign iv tgt src) = do
  tcUnifyTypes resTy mkTypeUnit
  (tgtTy, tgt') <- tcInferExprA tgt
  name <- case getLValueTarget tgt of
    Left l -> tcSetLoc l $ tcFatal "Invalid assignment target."
    -- Right n -> return n
    Right n | isJust (unLocated n) -> return $ fmap fromJust n
            | otherwise -> tcFatal "TODO: self not implemented."
  tgtId <- tcWrapLoc findVar name
  unless (idIsMutable $ unLocated tgtId) $
    flip tcWithLoc name $
    const $ tcAddErr $ "Cannot assign to immutable variable '" <>
      pprintName (unLocated name) <> "'."
  (srcTy, src') <- tcInferExprA src
  if iv == NotVectorized
    then tcUnifyTypes tgtTy srcTy
    else do
           (srcUnqualTy , _ , _) <- tcSplitQualifiedType srcTy
           localTy <- tcFreshQualifiedTy'
           tcAddWanted (PredSized localTy NoLocation)
           tcUnifyTypes srcUnqualTy (TArr localTy)
           tcUnifyTypes tgtTy srcTy
  return $ Assign iv tgt' src'

tcExpr resTy Hole =
  -- TODO: We should continue typing here and only raise error after
  -- constraints have been solved as far as possible. This could be achieved by
  -- adding a new constraint that doesn't advance constraint solving.
  tcThrowErr $ "Found hole of type " <> pretty resTy

tcExpr resTy (Index e slice) = tcIndexExpr resTy e slice

tcExpr resTy (Lam isf xs mt e) = do
  fResTy <- tcMaybeType mt
  fArgTys <- mapM (tcMaybeType . _lamParamType) xs
  tcUnifyTypes resTy (mkFunArgs fArgTys fResTy)
  let vars = [Located l (mkId x Immutable (typeToScheme t)) | (LamParam (Located l x) _, t) <- zip xs fArgTys]
  let xs' = zipWith LamParam vars (map Just fArgTys)
  tcSetVarSet (fromListUM' (map unLocated vars)) $
    tcLeaveForStmt $
      Lam isf xs' (Just fResTy) <$> tcExprA fResTy e

tcExpr resTy (List locList) = tcListExpr resTy locList

tcExpr resTy (Lit l) = do
  tcLit resTy l
  return $ Lit l

tcExpr resTy (RefArg e) = RefArg <$> tcExprA resTy e

tcExpr resTy (IndexStore s k) = do
  loc <- tcGetLoc
  (uVal, stage, dom) <- tcSplitQualifiedType resTy
  uKey <- tcFreshUnqualifiedTy
  let uStore = TStore uKey uVal `setLocation` loc
  let tyStore = mkQualifiedL uStore stage dom loc
  s' <- tcExprA tyStore s
  domKey <- tcFreshDomainTy
  let tyKey = mkQualifiedL uKey stage domKey loc
  k' <- tcExprA tyKey k
  tcAddWanted $ PredSub domKey dom loc
  return $ IndexStore s' k'

tcExpr resTy (StoreCtor kvs) = do
  loc <- tcGetLoc
  (u, s, d) <- tcSplitQualifiedType resTy
  uKey <- tcFreshUnqualifiedTy
  uVal <- tcFreshUnqualifiedTy
  tcAddWanted $ PredValidStore uKey uVal s loc
  let storeType = TStore uKey uVal `setLocation` loc
  tcUnifyTypes u storeType
  kvs' <- forM kvs $ \(k, v) -> do
    let go u e = do {
      dom <- tcFreshDomainTy;
      tcAddWanted $ PredSub d dom loc;
      tcExprA (mkQualifiedL u s dom loc) e }
    k' <- go uKey k
    v' <- go uVal v
    return (k', v')
  return $ StoreCtor kvs'

tcExpr resTy (StructCtor name ts fs) = tcStructCtor resTy name ts fs

tcExpr resTy (Select e comp) = tcSelectExpr resTy e comp

tcExpr resTy (Block stmts mresExpr) = tcBlock resTy stmts mresExpr

tcExpr resTy (Var name) = do
  mtyvar <- tcWrapLoc tcLookupType name
  case mtyvar of
    Located l (Just (k, TForAll{..})) | k == KindNat -> tcSetLoc l $ do
      case _typeSchemeType of
        TCon (ConNat (Finite n)) _ -> tcExpr resTy $ Lit $ ConstInt $ naturalToInteger n
        _ -> tcFatal "Unexpected type."
    _ -> do
      var <- tcWrapLoc findVar name
      if isId (unLocated var)
        then do
          tvs <- tcWithLoc (tcId resTy) var
          case tvs of
            [] -> return (Var var)
            _ -> do
              tyArgs <- tcTypeArguments [] tvs
              return $ Call NotVectorized (Func var) tyArgs []
        else if isTyVar (unLocated var)
          then tcWithLoc (tcTyVar resTy) var
          else tcAddErr errMsg >> return (Var var)
  where
    errMsg = "Type variable used where identifier is expected."

tcExpr resTy (Tuple es) = do
  (ts, es') <- unzip <$> mapM tcInferExprA es
  l <- tcGetLoc
  let u = TApp (mkCon (ConTuple (length ts))) ts l
  tupleDom <- tcFreshDomainTy
  let tupleType = mkQualifiedL u mkPre tupleDom l
  tcUnifyTypes resTy tupleType
  forM_ ts $ \elemTy -> do
    (_, _, elemDom) <- tcSplitQualifiedType elemTy
    tcEmitStructComponentConstr elemDom tupleType
  return $ Tuple es'

tcExpr resTy (Cast e t) = do
  (k, t') <- tcInferTypeKind t
  case k of
    KindDomain -> tcCastDomain resTy e t'
    KindStage -> tcCastStage resTy e t'
    KindUnqualified -> tcCastType resTy e t'
    _ -> tcThrowErr $
      "Invalid type cast of kind" <+> pretty k <> "." $$
      "Only domain, stage and unqualified data types are supported."

tcExpr resTy (DbgAssert e1 me2) = do
  l <- tcGetLoc
  r <- tcFreshRingTy
  let t = mkUnqualBin r
  d <- tcFreshDomainTy
  let binTy = mkQualifiedL t mkPre d l
  let strTy = mkQualifiedL (mkCon ConString) mkPre d l
  e1' <- tcExprA binTy e1
  me2' <- traverse (tcExprA strTy) me2
  tcUnifyTypes resTy mkTypeUnit
  return $ DbgAssert e1' me2'

tcExpr resTy (DbgAssertEq e1 e2 me3) = do
  l <- tcGetLoc
  r <- tcFreshRingTy
  let t = mkUnqualInt r
  d <- tcFreshDomainTy
  let intTy = mkQualifiedL t mkPre d l
  let strTy = mkQualifiedL (mkCon ConString) mkPre d l
  e1' <- tcExprA intTy e1
  e2' <- tcExprA intTy e2
  me3' <- traverse (tcExprA strTy) me3
  tcUnifyTypes resTy mkTypeUnit
  return $ DbgAssertEq e1' e2' me3'

tcExpr resTy (ExprLoc l e) = ExprLoc l <$> tcSetLoc l (tcExpr resTy e)

tcExpr resTy (IfThenElse e1 e2 e3) = do
  let brLoc = location e1
  case exprToTypePred e1 of
    Just p -> do
      p' <- tcTypePred p
      case p' of
        PredPostRing r _            -> tcAddWanted (PredTestPostRing r NoLocation)
        PredPostConvertible r1 r2 _ -> tcAddWanted (PredTestPostConvertible r1 r2 NoLocation)
        PredChallenge r _           -> tcAddWanted (PredTestChallenge r NoLocation)
        PredExtendedArithmetic _    -> tcAddWanted (PredTestExtendedArithmetic NoLocation)
        PredObliviousChoice _       -> tcAddWanted (PredTestObliviousChoice NoLocation)
        PredPermutationCheck _      -> tcAddWanted (PredTestPermutationCheck NoLocation)
        PredVectors _               -> tcAddWanted (PredTestVectors NoLocation)
        _                           -> return ()
      tcWithNextLevel $
        tcSetBranchDomain mkPublicDomain $ do
          let unitExpr = Lit ConstUnit
          (wt, e2') <- tcCollectWanted $ tcExprA resTy e2
          (wf, e3') <- tcCollectWanted $ tcExprA resTy (fromMaybe unitExpr e3)
          let negP = tryNegateTypePred p'
          when (null negP && isNothing e3) $
            tcSetLoc (location e1) $
              tcAddWarn "Unable to negate a type-level conditional. This may cause futher type errors."
          tcAddImplication negP wf
          tcAddImplication [p'] wt
          return (TypeIf p' e2' e3')
    Nothing -> do
      natTy <- tcSetLoc brLoc tcFreshNatTy
      condDomTy <- tcSetLoc brLoc tcFreshDomainTy
      let condTy = mkQualifiedL (mkUnqualBin (mkPlain natTy)) mkPre condDomTy brLoc
      e1' <- tcExprA condTy e1
      tcSetBranchDomain condDomTy $ do
        e2' <- tcExprA resTy e2
        e3' <- traverse (tcExprA resTy) e3
        return $ IfThenElse e1' e2' e3'

tcExpr resTy (Match e cases) = do
  loc <- tcGetLoc
  tcAddWanted (PredObliviousChoice loc)
  let topLoc = location e
  ringTy <- tcSetLoc topLoc tcFreshRingTy
  tcAddWanted (PredPostRing ringTy topLoc)
  topDomTy <- tcSetLoc topLoc tcFreshDomainTy
  let topTy = mkQualifiedL (mkUnqualInt ringTy) mkPost topDomTy topLoc
  e' <- tcExprA topTy e
  tcSetBranchDomain topDomTy $ Match e' <$> traverse (tcCase (ringTy, resTy)) cases
  
tcExpr _resTy (Call _ Method{} _vs _es) = tcFatal "TODO: method calls not implemented"

tcExpr resTy (Call iv (Func f) vs es) = do
  tcDebugPrint ("Type checking call of function" <+> pretty f)
  (ts, es') <- unzip <$> mapM tcInferExprA es
  let ts' | null ts = [mkTypeUnit]
          | otherwise = ts
  let funcType = mkFunArgs ts' resTy
  (f', tyParams) <- if iv == NotVectorized
                      then tcWrapFstLoc (tcFunCallName funcType) f
                      else flip tcWrapFstLoc f $ \ f -> do
                             let fst3 (u , _ , _) = u
                             resUnqualTy : us <- fmap fst3 <$> traverse tcSplitQualifiedType (resTy : ts')
                             localArgTys <- traverse (const tcFreshQualifiedTy') es
                             localResTy <- tcFreshQualifiedTy'
                             loc <- tcGetLoc
                             tcAddWanted (PredVectorization loc)
                             traverse_ (tcAddWanted . flip PredSized loc) $ localResTy : localArgTys
                             zipWithM_ tcUnifyTypes (resUnqualTy : us) (fmap TArr (localResTy : localArgTys))
                             let localFuncType = mkFunArgs localArgTys localResTy
                             tcFunCallName localFuncType f
  let fName = varName (unLocated f')
  -- Verify by-ref arguments
  mParams <- tcGetTopFunParams (unLocated f')
  params <- case mParams of
    Just params | PassByRef `elem` params -> do
      unless (length es' == length params) $
        tcFatal "Functions with by-ref parameters can not be partially applied."
      return params
    _ -> return $ replicate (length es') PassByValue
  zipWithM_ checkArgPassedVia es' params
  tyArgs <- tcTypeArguments vs tyParams
  let isGetArg = isBuiltin fName && nameBuiltinInfo fName `elem`
                 [BuiltinGetWitness, BuiltinGetInstance, BuiltinGetPublic]
  let call = Call iv (Func f') tyArgs es'
  return $ if isGetArg
    then TypeAnnot resTy call
    else call

tcExpr resTy (While cond body) = do
  let l = location cond
  natTy <- tcSetLoc l tcFreshNatTy
  d <- tcSetLoc l tcFreshDomainTy
  let boolTy = mkQualifiedL (mkUnqualBin (mkPlain natTy)) mkPre d l
  cond' <- tcExprA boolTy cond
  body' <- tcSetInForStmt $ tcExprA mkTypeUnit body
  tcUnifyTypes resTy mkTypeUnit
  return $ While cond' body'

tcExpr resTy (WireExpr shapeExpr e) = do
  (shapeTy, shapeExpr') <-
    tcSetLoc (location shapeExpr) $ tcInferExprA shapeExpr

  (fromTy, e') <- tcSetLoc (location e) $ tcInferExprA e

  let loc = joinLocations (location shapeExpr) (location e)
  tcAddWanted $ PredWireExpr shapeTy fromTy resTy loc

  return $ WireExpr shapeExpr' e'

tcExpr resTy (For i e1 e2 e3) = tcForExpr resTy i e1 e2 e3

tcExpr resTy (TypePredExpr p) = do
  tcUnifyTypes resTy mkTypePubBool
  TypePredExpr <$> tcTypePred p

tcExpr resTy (Trace str e) = Trace str <$> tcExprA resTy e

tcExpr resTy (Zip pairs e) = tcZipExpr resTy pairs e

tcExpr _resTy CallOper{} =
  tcICE "Unexpected CallOper. Should be desugared away."

tcExpr _resTy TypeAnnot{} =
  tcICE "Unexpected TypeAnnot. Internal, should only be generated by tcExpr."

tcExpr _resTy TypeIf{} =
  tcICE "Unexpected TypeIf. Internal, should only be generated by tcExpr."

tcExpr _resTy TypeToExpr{} =
  tcICE "Unexpected TypeToExpr. Internal, should only be generated by tcExpr."

tcExpr _resTy Self{} =
  tcICE "Unexpected TSelf. Not implemented yet."

tcCase :: (NatType Var, QualifiedType Var) -> (Located (Pat Name), Expr Name) -> TcM (Located (Pat Var), Expr Var)
tcCase (natTy, resTy) (lhs, rhs) 
  = tcLHS natTy lhs $ \ lhs' -> {- do
      (ws , res) <- tcCollectWanted $ tcExprA resTy rhs
      let typePreds = toListOf typePredInWantedConstraints ws
      traverse_ (tcUnifyTypes natTy) (extractFields typePreds)
      tcAndWanted ws
      return (lhs' , res)
-}
    (lhs' ,) <$> tcExprA resTy rhs


tcLHS :: NatType Var -> Located (Pat Name) -> (Located (Pat Var) -> TcM a) -> TcM a
tcLHS natTy (Located l pat) cont = case pat of
  LitPat n    -> cont (Located l (LitPat n))
  VarPat name -> let x = mkId name Immutable (typeToScheme natTy) in
                 tcSetLoc l $ tcSetVar name x $ cont (Located l (VarPat x))
  WildCard    -> cont (Located l WildCard)

isRefArg :: Expr a -> Bool
isRefArg (RefArg _) = True
isRefArg (ExprLoc _ e) = isRefArg e
isRefArg (TypeAnnot _ e) = isRefArg e
isRefArg (Ascription e _) = isRefArg e
isRefArg _ = False

-- Check if a function argument can be passed via given calling convention.
checkArgPassedVia :: Expr Var -> ParamPassingStyle -> TcM ()
checkArgPassedVia e = \case
  PassByValue ->
    when refArg $
      tcSetLoc exprLoc $
        tcFatal "Immutable parameter can not be passed by reference."
  PassByRef -> do
    unless refArg $
      tcSetLoc exprLoc $
        tcFatal "Missing \'ref\' annotation in call site when passing by-ref parameter."
    Located l var <- case getLValueTarget e of
      Left l ->
        tcSetLoc l $ tcFatal "Only rvalues can be passed by reference."
      Right lvar -> return lvar
    case var of
      Nothing -> tcFatal "TODO: self not implemented."
      Just var ->
        unless (idIsMutable var) $
          tcSetLoc l $
            tcFatal "Only mutable variables can be passed by reference."
  where
    refArg = isRefArg e
    exprLoc = locOfAnnotExpr e

structsOf :: Expr Name -> Type Var -> TcM [(Expr Name , StructEnv)]
structsOf offsetVar typ
  = case typ of
      TQualify u _ _
        -> structsOf offsetVar u
      TList t
        -> structsOf (Index offsetVar (noLoc (ArrayIndex (Lit (ConstInt 0))))) t
      TArr t
        -> structsOf (Index offsetVar (noLoc (ArrayIndex (Lit (ConstInt 0))))) t
      TTuple ts
        -> do
             substructs <- zipWithM (\ i t -> structsOf (Select offsetVar (SelectIndex i)) t) [0 .. ] ts
             return (concat substructs)
      _ -> do
             isStruct <- tcIsStruct typ
             if isStruct
               then do
                 structEnv <- tcFindStruct . varName . unLocated . fromJust . extractHeadVar $ typ
                 let fields = M.elems . _structFields $ structEnv
                 substructs <- mapM (\ StructFieldInfo{..} -> structsOf (Select offsetVar (SelectField _fieldName)) _fieldType) fields
                 return (foldr (++) [(offsetVar , structEnv)] substructs)
               else return []

tcBlock :: QualifiedType Var -> [Stmt Name] -> Maybe (Expr Name) -> TcM (Expr Var)
tcBlock resTy statementList mresExpr = go statementList []
  where
    go [] stmts' = do
      resExpr <- tcExprA resTy $ fromMaybe (Lit ConstUnit) mresExpr

      -- Type check a fictive call to finalizer for all finalized variables
      loc <- tcGetLoc
      let mutVars = filter (idIsMutable . unLocated) . mapMaybe varsDefinedInStmt $ stmts'
      let mutVarNames = fmap ((\ name -> Located (nameLocation name) name) . varName . unLocated) mutVars
      let mutVarTypes = fmap (_typeSchemeType . idType . unLocated) mutVars
      tcDebugPrint ("mutVarNames =" <+> pretty mutVarNames)
      tcDebugPrint ("mutVarTypes =" <+> pretty mutVarTypes)
      (structs , structEnvs) <- unzip . concat <$> zipWithM structsOf (fmap Var mutVarNames) mutVarTypes
      tcDebugPrint ("Searching for finalizers of" <+> pretty (length structEnvs) <+> "structs" <+> hcat (punctuate ", " (fmap (pretty . nameOccName . _structName) structEnvs)))
      let exprFinAssocs = mapMaybe (\ (a , b) -> (a ,) <$> b) . zip structs . fmap _structFinalizer $ structEnvs
      let fictiveCalls = fmap (\ (expr , fin) -> Call NotVectorized (Func (Located loc fin)) [] [expr]) exprFinAssocs
      _ <- mapM (\ call@ (Call _ _ _ [arg]) -> tcDebugPrint ("Type checking finalization of" <+> pretty (fromJust . unLocated . fromRight undefined . getLValueTarget $ arg) <+> "or its part") >> tcExpr mkTypeUnit call) fictiveCalls
      return $ Block (reverse stmts') (Just resExpr)

    go (stmt : stmts) stmts' = tcStmt stmt (\stmt' -> go stmts (stmt' : stmts'))

tcSplitQualifiedType :: QualifiedType Var -> TcM (UnqualifiedType Var, StageType Var, DomainType Var)
tcSplitQualifiedType (TQualify u s d) = return (u, s, d)
tcSplitQualifiedType t = do
  l <- tcGetLoc
  res@(u, s, d) <- tcFreshQualifiedTy
  tcUnifyTypes t (mkQualifiedL u s d l)
  return res

-- tcEmitStructComponentConstr elemDomain fieldType
tcEmitStructComponentConstr :: DomainType Var -> QualifiedType Var -> TcM ()
tcEmitStructComponentConstr elemDomain structTy = do
  l <- tcGetLoc
  (_, _, structDomain) <- tcSplitQualifiedType structTy
  tcAddWanted $ PredSub structDomain elemDomain l

-- TODO: allow negation of 'pre' and 'post'?
-- Care must be taken because in a general case negations aren't solvable.
exprToTypePred :: Expr a -> Maybe (TypePred a)
exprToTypePred (ExprLoc _ e) = exprToTypePred e
exprToTypePred (TypePredExpr p) = Just p
exprToTypePred (TypeAnnot _ e) = exprToTypePred e
exprToTypePred _ = Nothing

tcStmt :: Stmt Name -> (Stmt Var -> TcM a) -> TcM a
tcStmt (Expr e) cont =
  case viewForExpr e of
    Just (x, e1, e2, e3) -> tcForStmt x e1 e2 e3 cont
    Nothing -> do
      e' <- tcExprA mkTypeUnit e
      cont (Expr e')
tcStmt (Let b (Binding m (Located l x) mt) e) cont = tcSetLoc l $ do
  t' <- tcMaybeType mt
  when (b && m == Mutable) $
    tcThrowErr "Recursively defined variables are not allowed to be mutable."
  when (m == Mutable) $
    tcAddWanted $ PredMutableVariable t' l
  let x' = mkId x m (typeToScheme t')
  tcSetVar x x' $ do
    e' <- tcExprA t' e -- renamer differentiates between recursive and nonrecursive
    cont $ Let b (Binding m (Located l x') (Just t')) e'
tcStmt (Break l) cont = tcSetLoc l $ do
  inLoop <- tcIsInForStmt
  unless inLoop $ tcThrowErr "Break may only occur inside a for statement."
  cont $ Break l
tcStmt (Continue l) cont = tcSetLoc l $ do
  inLoop <- tcIsInForStmt
  unless inLoop $ tcThrowErr "Continue may only occur inside a for statement."
  cont $ Continue l
tcStmt (Return e) cont = do
  retTy <- tcGetReturnType
  e' <- tcExprA retTy e
  cont $ Return e'

tcForExpr :: QualifiedType Var -> Located Name -> Expr Name -> Expr Name -> Expr Name -> TcM (Expr Var)
tcForExpr resTy (Located l i) e1 e2 e3 = do
  (rangeTy, domTy) <- tcSetLoc l  tcFreshPreU64
  let i' = mkId i Immutable (typeToScheme rangeTy)
  e1' <- tcExprA rangeTy e1
  e2' <- tcExprA rangeTy e2
  (t, e3') <- tcSetVar i i' $ tcInferExprA e3
  tcUnifyTypes (mkTypeList t domTy) resTy
  return $ For (Located l i') e1' e2' e3'

tcZipExpr :: QualifiedType Var -> [(Located Name, Expr Name)] -> Expr Name -> TcM (Expr Var)
tcZipExpr resTy pairs e = do
  l <- tcGetLoc
  tcAddWanted (PredVectorization l)
  resArrDom <- tcFreshDomainTy
  let (xs, _xss) = unzip pairs
  (xs', xss') <- fmap unzip $ forM pairs $ \ (x, xs) -> do
    ty <- tcFreshQualifiedTy'
    let x' = case x of Located l x -> Located l $ mkId x Immutable (typeToScheme ty)
    (arrTy, xs') <- tcInferExprA xs
    argArrDom <- tcFreshDomainTy
    tcAddWanted $ PredSub argArrDom resArrDom l
    tcUnifyTypes (mkTypeArr ty argArrDom) arrTy
    return (x', xs')
  (t, e') <- tcSetVars (zip (map unLocated xs) (map unLocated xs')) $ tcInferExprA e
  tcUnifyTypes (mkTypeArr t resArrDom) resTy
  return $ Zip (zip xs' xss') e'

tcForStmt :: Located Name -> Expr Name -> Expr Name -> Expr Name -> (Stmt Var -> TcM a) -> TcM a
tcForStmt (Located l i) e1 e2 e3 cont = do
  (rangeTy, domTy) <- tcSetLoc l tcFreshPreU64
  let i' = mkId i Immutable (typeToScheme rangeTy)
  e1' <- tcExprA rangeTy e1
  e2' <- tcExprA rangeTy e2
  (t, e3') <- tcSetVar i i' $ tcSetInForStmt $ tcSetBranchDomain domTy $ tcInferExprA e3
  let resTy = mkTypeUnit
  tcUnifyTypes resTy t
  cont $ Expr $ TypeAnnot resTy $ For (Located l i') e1' e2' e3'

tcMaybeType :: Maybe (Type Name) -> TcM (QualifiedType Var)
tcMaybeType Nothing = tcFreshQualifiedTy'
tcMaybeType (Just t) = tcType KindStar t

tcCastDomain :: QualifiedType Var -> Expr Name -> DomainType Var -> TcM (Expr Var)
tcCastDomain resTy e dom = do
  (t, s, d) <- tcFreshQualifiedTy
  let eTy = mkQualified t s d
  --tcUnifyTypes resTy (mkQualified t s dom)
  --tcUnifyTypes resTy (TCast eTy dom)
  tcUnifyTypes resTy (mkQualified (TCastUnqual t dom) s dom)
  e' <- tcExprA eTy e
  tcAddSubConstr d dom -- make sure that d <= dom
  return $ Cast e' dom

tcCastType :: QualifiedType Var -> Expr Name -> UnqualifiedType Var -> TcM (Expr Var)
tcCastType resTy e tarTy = do
  (t, s, d) <- tcFreshQualifiedTy
  let eTy = mkQualified t s d
  tcUnifyTypes resTy (mkQualified tarTy s d)
  e' <- tcExprA eTy e
  loc <- tcGetLoc
  tcAddWanted $ PredConvertibleTo eTy tarTy loc
  return $ Cast e' tarTy

tcCastStage :: QualifiedType Var -> Expr Name -> StageType Var -> TcM (Expr Var)
tcCastStage resTy e tarStage = do
  (t, s, d) <- tcFreshQualifiedTy
  let eTy = mkQualified t s d
  tcUnifyTypes resTy (mkQualified t tarStage d)
  e' <- tcExprA eTy e
  return $ Cast e' tarStage

tcLit :: Type Var -> Constant -> TcM ()
tcLit resTy (ConstInt _) = do
  (u, _, _) <- tcSplitQualifiedType resTy
  ringTy <- tcFreshRingTy
  tcUnifyTypes u (mkUnqualInt ringTy)
tcLit resTy (ConstBool _) = do
  (u, _, _) <- tcSplitQualifiedType resTy
  ringTy <- tcFreshRingTy
  tcUnifyTypes u (mkUnqualBin ringTy)
tcLit resTy (ConstString _) = do
  d <- tcFreshDomainTy
  let strTy = mkQualified (mkCon ConString) mkPre d
  tcUnifyTypes resTy strTy
tcLit resTy ConstUnit =
  tcUnifyTypes resTy mkTypeUnit

tcSelectExpr :: Type Var -> Expr Name -> Selector -> TcM (Expr Var)
tcSelectExpr resTy e comp = do
  ~(t, e') <- tcInferExprA e
  loc <- tcGetLoc
  let s = case comp of
            SelectField x -> Right x
            SelectIndex i -> Left i
  tcAddWanted $ TypePred (PConHasField s) [t, resTy] loc
  return $ Select e' comp

-- With: struct name { y1 : t1, ..., ym : em }
-- Type check:
-- name { x1 : e1, ..., xn : en } : resTy
tcStructCtor
  :: QualifiedType Var
  -> Located Name
  -> [TypeArgument Name]
  -> [StructFieldCtor Name]
  -> TcM (Expr Var)
tcStructCtor resTy (Located l name) ts fs = do
  structVar <- tcFindTyVar name
  StructEnv{..} <- tcFindStruct name
  let TForAll vs preds ty = _structType
  unless (null preds) $
    tcFatal "TODO: tcStructCtor: Type predicates."
  (subst, us) <- tcSubFresh vs
  ts' <- tcTypeArguments ts us
  let structTyArgs = map (\v -> TVar v (tyVarKind v) (location v)) us
  let structUnqualTy = mkTApp (subType subst ty) structTyArgs
  structTy <- mkQualified structUnqualTy mkPre <$> tcFreshDomainTy
  tcUnifyTypes resTy structTy
  tcThrowIfErrs $ do
    -- Check if all struct fields have been defined.
    let definedFields = S.fromList [n | StructFieldCtor (Located _ n) _ <- fs]
    forM_ _structFields $ \StructFieldInfo{..} ->
      unless (S.member _fieldName definedFields) $
        tcAddErr $ "Field" <+> pretty _fieldName <+> "not defined."
    -- Check if expressions type check and we are defining correct fields.
    unordFields <- forM fs $ \(StructFieldCtor lname e) -> do
      let fieldName = unLocated lname
      case M.lookup fieldName _structFields of
        Nothing -> do
          tcAddErr $ "No field named" <+> pretty fieldName <+> "."
          e' <- snd <$> tcInferExprA e -- Just make stuff up!
          -- No reason to emit field component constraints as this anyways will yield an error.
          return (maxBound :: Int, StructFieldCtor lname e')
        Just StructFieldInfo{..} -> do
          let fieldType = subType subst _fieldType
          (_, _, elemDom) <- tcSplitQualifiedType fieldType
          tcEmitStructComponentConstr elemDom structTy
          e' <- tcExprA fieldType e
          return (_fieldPos, StructFieldCtor lname e')
    let ordFields = map snd $ sortOn fst unordFields -- order fields by their position
    return $ StructCtor (Located l structVar) ts' ordFields

tcIndexExpr :: Type Var -> Expr Name -> LArraySlice (Expr Name) -> TcM (Expr Var)
tcIndexExpr resTy expr locSlice = do
  loc <- tcGetLoc
  (slice', indexDom) <- tcWrapFstLoc tcSliceExpr locSlice
  elemType <- case unLocated slice' of
    ArrayIndex {} -> return resTy
    _             -> tcFreshQualifiedTy'
  let arrayDom = indexDom
  arrayCon <- tcFreshMetaTy (KindFun KindStar KindUnqualified)
  let arrayUnqualified = TApp arrayCon [elemType] loc
  let arrayType = mkQualified arrayUnqualified mkPre arrayDom
  tcAddWanted $ PredArray arrayCon loc
  expr' <- tcExprA arrayType expr
  case unLocated slice' of
    ArrayIndex {} -> return ()
    _             -> tcUnifyTypes resTy arrayType
  return $ Index expr' slice'

tcSliceExpr :: ArraySlice (Expr Name) -> TcM (ArraySlice (Expr Var), DomainType TyVar)
tcSliceExpr slice = do
  (t, domTy) <- tcFreshPreU64
  slice' <- traverse (tcExprA t) slice
  return (slice', domTy)

tcListExpr :: QualifiedType Var -> List (Expr Name) -> TcM (Expr Var)
tcListExpr resTy lst = do
  l <- tcGetLoc
  (lstU, lstS, lstD) <- tcSplitQualifiedType resTy
  tcUnifyTypes lstS mkPre
  (elemTy, lst') <- case lst of
    ListRange a b -> do
      (elemTy, elemD, _) <- tcFreshPreUintN
      tcAddWanted $ PredSub lstD elemD l
      a' <- tcExprA elemTy a
      b' <- tcExprA elemTy b
      return (elemTy, ListRange a' b')
    ListElems xs -> do
      (t, s, d) <- tcFreshQualifiedTy
      let elemTy = mkQualifiedL t s d l
      xs' <- mapM (tcExprA elemTy) xs
      tcAddWanted $ PredSub lstD d l
      return (elemTy, ListElems xs')
    ListReplicate val times -> do
      (t, s, d) <- tcFreshQualifiedTy
      let elemTy = mkQualifiedL t s d l
      val' <- tcExprA elemTy val
      (lenTy, lenDomTy) <- tcFreshPreU64
      tcUnifyTypes lstD lenDomTy
      times' <- tcExprA lenTy times
      return (elemTy, ListReplicate val' times')
  tcUnifyTypes lstU (TApp (mkCon ConList) [elemTy] l)
  return $ List lst'

{----------------------
 -- Helper functions --
 ----------------------}

tcId :: Type Var -> Var -> TcM [TyVar]
tcId resTy var = do
  let scheme = idType var
  if nameOccName (varName var) == "finalize" then tcDebugPrint ("Type checking finalizer identifier of type" <+> pretty scheme) else return ()
  let hasStages =
        null [ s | s@(TCon ConNoStage _) <-
                   universe (scheme ^. typeSchemeType)
             ]
  unless hasStages $
    tcThrowErr $ "Could not infer stage types of function" <+> pretty var <> ". Specify stages in the signature."

  (preds, varTy, vs) <- instantiateType $ idType var
  loc <- tcGetLoc
  let preds' = [p `setLocation` loc | p <- preds]
  mapM_ tcAddWanted preds'
  tcUnifyTypes resTy varTy
  return vs

tcFunCallName :: Type Var -> Name -> TcM (Var, [TyVar])
tcFunCallName resTy name = do
    var <- findVar name
    if isId var
      then (var,) <$> tcId resTy var
      else tcThrowErr "Type variable used where function is expected."

tcTyVar :: QualifiedType Var -> TyVar -> TcM (Expr Var)
tcTyVar resTy var
  | tyVarKind var == KindNat = do
    l <- tcGetLoc
    (u, _, _) <- tcSplitQualifiedType resTy
    tcUnifyTypes u $ TApp (TCon ConInt l) [TApp (TCon ConPlain l) [TCon (ConNat Infinite) l] l] l
    return $ TypeToExpr (TVar var KindNat l)
  | otherwise = tcThrowErr "Only type variables with Nat kind may occur in expressions."

tcInferExprA :: Expr Name -> TcM (Type Var, Expr Var)
tcInferExprA e = do
  (t, e') <- tcInferExpr e
  return (t, TypeAnnot t e')

tcInferExpr :: Expr Name -> TcM (Type Var, Expr Var)
tcInferExpr e = do
  t <- tcFreshQualifiedTy'
  e' <- tcExpr t e
  return (t, e')

tcFreshPreU64 :: TcM (QualifiedType TyVar, DomainType TyVar)
tcFreshPreU64 = do
  domTy <- tcFreshDomainTy
  return (mkTypeU64 mkPre domTy, domTy)

tcFreshPreUintN :: TcM (QualifiedType TyVar, DomainType TyVar, NatType TyVar)
tcFreshPreUintN = do
  domTy <- tcFreshDomainTy
  natTy <- tcFreshNatTy
  return (mkTypeUIntMod natTy mkPre domTy, domTy, natTy)

tcFreshNatTy :: TcM (NatType Var)
tcFreshNatTy = tcFreshMetaTy KindNat

tcFreshRingTy :: TcM (RingType Var)
tcFreshRingTy = tcFreshMetaTy KindRing

-- Location of expression that has been type annotated.
-- Useful if we need to get expression location after type checking.
locOfAnnotExpr :: HasLocation a => Expr a -> Location
locOfAnnotExpr (Var a) = location a
locOfAnnotExpr (TypeAnnot _ e) = locOfAnnotExpr e
locOfAnnotExpr (ExprLoc l _) = l
locOfAnnotExpr _ = NoLocation

findFunType
  :: T.Text -> TypedProgram -> Maybe (TypeScheme Var)
findFunType str
  = lookup str .
    fmap (\ x -> (nameOccName (varName x) , idType x)) . 
    fmap _tFunName . 
    flattenSCCs . 
    _tProgFunctions

nameOrLit :: Type Var -> Either Name ExtendedNatural
nameOrLit (TVar x _ _) = Left (tyVarName x)
nameOrLit (TNat n)     = Right n
nameOrLit _            = error "nameOrLit: Unreachable"

matchMatch :: Expr a -> (Expr a , [(Located (Pat a) , Expr a)])
matchMatch (Match e cases)
  = (e , cases)
matchMatch _
  = error "matchMatch: Unreachable"

extractNat :: QualifiedType a -> Type a
extractNat (TQualify (TUInt n) _ _)
  = n
extractNat (TQualify (TBool n) _ _)
  = n
extractNat _
  = error "unqualify: Unreachable"

-- Finds all fields used in function body, including type variables of kind Nat
fieldsUsedByFun
  :: TypedTopFunction -> [(Location , [Type Var])]
fieldsUsedByFun fun
  = let
      matchExprs
        = toListOf traverseMatchInExpr $ _tFunBody $ fun
      caseslocation match
        = let (_ , cases) = matchMatch match in
          foldr joinLocations NoLocation $ fmap (\ (lhs , rhs) -> location lhs `joinLocations` location rhs) cases
      matchKindNatAtoms match
        = let (e , cases) = matchMatch match in
          concatMap (toListOf kindNatInType) (getExprType e : concatMap (toListOf traverseTypeInExpr) (fmap snd cases))
    in
    zip (fmap caseslocation matchExprs) . fmap (fmap head . groupBy ((==) `on` nameOrLit) . sortOn nameOrLit . fmap extractNat) $
    fmap matchKindNatAtoms matchExprs

