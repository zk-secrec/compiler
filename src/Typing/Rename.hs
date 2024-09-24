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

module Typing.Rename (rename, rnProgram) where

import Basic.Location
import Basic.Message
import Basic.Name
import Parser.Syntax
import Parser.Effect
import Support.Pretty
import Typing.TcM

import Control.Lens (_2, (%~), (^.), both, traverseOf)
import Control.Monad (forM_, when, zipWithM)
import Data.List (find, nub)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe, catMaybes)
import Data.Text (Text)


{----------------------------
 -- Some utility functions --
 ----------------------------}

-- If the given occurs name is not in scope then we emit an error but continue
-- with renaming. This is to grab as many errors as possible.
checkName :: Text -> TcM Name
checkName occ = do
  mname <- tcLookupVarOccName occ
  case mname of
    Just name -> return name
    Nothing -> do
      mname' <- tcLookupTypeOccName occ
      case mname' of
        Just name -> return name
        Nothing -> tcThrowErr $ "Name" <+> pretty occ <+> "not in scope."

checkTypeName :: Text -> TcM Name
checkTypeName occ = do
  mname <- tcLookupTypeOccName occ
  case mname of
    Just name -> return name
    Nothing -> tcThrowErr $ "Type name" <+> pretty occ <+> "not in scope."

setNamesGeneric :: (Text -> Name -> TcM a -> TcM a) -> [Located Text] -> TcM a -> TcM a
setNamesGeneric _f [] tcm = tcm
setNamesGeneric f (occ : ns) tcm = do
  name <- tcWithLoc tcFreshName occ
  f (unLocated occ) name (setNamesGeneric f ns tcm)

setNamesGeneric' :: (Text -> Name -> TcM a -> TcM a) -> [Located Name] -> TcM a -> TcM a
setNamesGeneric' _f [] tcm = tcm
setNamesGeneric' f (n : ns) tcm = do
  let name = unLocated n
  f (nameOccName name) name (setNamesGeneric' f ns tcm)

setGlobalNames :: [Located Text] -> TcM a -> TcM a
setGlobalNames = setNamesGeneric tcBindTypeOccName

setNames :: [Located Text] -> TcM a -> TcM a
setNames = setNamesGeneric tcBindVarOccName

withName :: Located Text -> (Located Name -> TcM a) -> TcM a
withName (Located loc occ) cont = do
  name <- tcSetLoc loc $ tcFreshName occ
  tcBindVarOccName occ name (cont (Located loc name))

withNames :: [Located Text] -> ([Located Name] -> TcM a) -> TcM a
withNames ts f = g ts []
  where
    g [] ns = f (reverse ns)
    g (t : ts) ns = withName t $ \ n -> g ts (n : ns)

-- Need this for both bag and list
buildLocMap :: (Foldable t, Ord a) => t (Located a) -> Map.Map a [Location]
buildLocMap = foldr addName Map.empty
  where
    addName (Located l n) = Map.insertWith (++) n [l]

{---------------------
 -- Actual renaming --
 ---------------------}

setTopLevelNames :: ([LTypeDef Name], [LStructDecl Name], [LSignature Name], [LFunction Name], [LStructImpl Name])
  -> Program Text -> TcM a -> TcM a
setTopLevelNames (tsi, ssi, esi, fsi, isi) Program{..} cont = do
  env <- getEnv
  let moduliTypeNames = map (noLoc . fst) $ Map.toList (env ^. tcTypeRnEnv)
  -- Same method name in different struct impls must be allowed
  checkForDuplicates (topFunNames ++ map occ funNamesI)
  --checkForDuplicates (funNames ++ map occ funNamesI)
  checkForDuplicates (moduliTypeNames ++ typeNames ++ map occ typeNamesI ++ structNames ++ map occ structNamesI)
  setNamesGeneric' tcBindVarOccName funNamesI $
    setNamesGeneric' tcBindTypeOccName (typeNamesI ++ structNamesI) $
      setNamesGeneric tcBindTypeOccName (typeNames ++ structNames) $
        setNames funNames cont
  where
    -- funs consts types cont
    occ = fmap nameOccName
    typeNamesI = map (_tyDefName . unLocated) tsi
    structNamesI = map (_structDeclName . unLocated) ssi
    funNamesI = map extName esi ++ map funName fsi ++ concatMap (map funName . _structImplBody . unLocated) isi

    extName = _sigName . unLocated
    funName = _sigName . unLocated . _funSignature . unLocated
    funNames = topFunNames ++ concatMap (map funName . _structImplBody . unLocated) _programStructImpls
    topFunNames = map extName _programTopExterns ++ map funName _programTopFunctions
    typeNames = map (_tyDefName . unLocated) _programTypeDefs
    structNames = map (_structDeclName . unLocated) _programStructDecls

rename :: [Module (LProgram Name)] -> Module (LProgram Text) -> TcM [Module (LProgram Name)]
rename modules (lprog, name, imports) = do
  lprog' <- tcThrowIfErrs $ do
    tcWrapLoc (rnProgram (impTys, impStructs, impExts, impFuns, impImpls)) lprog
  return $ (lprog', name, imports) : modules
  where
    isPublicFun = _sigIsPublic . unLocated . _funSignature . unLocated
    isPublicExt = _sigIsPublic . unLocated
    findModule imp = find (\(_, name, _) -> imp == name) modules
    impMods = mapMaybe findModule imports
    impProgs = map (\(p, _, _) -> unLocated p) impMods
    impExts =
      filter isPublicExt $
      concatMap _programTopExterns impProgs
    impFuns =
      filter isPublicFun $
      concatMap _programTopFunctions impProgs
    impTys =
      filter (_tyDefIsPublic . unLocated) $
      concatMap _programTypeDefs impProgs
    impStructs =
      filter (_structDeclIsPublic . unLocated) $
      concatMap _programStructDecls impProgs
    impImpls =
      map (fmap (structImplBody %~ filter isPublicFun)) $
      concatMap _programStructImpls impProgs

rnSignature :: Located Name -> Signature Text -> TcM (Signature Name)
rnSignature name Signature {..} = do
  tyParams <- tcWrapLoc (mapM rnTypeParam) _sigTypeParameters
  constr <- tcWrapLoc (mapM rnTypePred) _sigConstraints
  params <- tcWrapLoc (mapM rnFuncParam) _sigParameters
  retTy <- rnType _sigReturnType
  effect <- traverse (tcWrapLoc rnPolyTwe) _sigEffect
  return $ Signature { _sigName = name
                     , _sigIsPublic = _sigIsPublic
                     , _sigTypeParameters = tyParams
                     , _sigParameters = params
                     , _sigConstraints = constr
                     , _sigReturnType = retTy
                     , _sigIsOperator = False
                     , _sigFixity = Nothing
                     , _sigEffect = effect
                     }

rnFuncParam :: FuncParam Text -> TcM (FuncParam Name)
rnFuncParam (FuncParam ps occ ty) = do
  name <- checkLName occ
  ty' <- rnType ty
  return $ FuncParam ps name ty'
rnFuncParam (SelfParam ps loc) = tcSetLoc loc $
                                 tcIfSelfAllowed "parameter" $ 
                                 return $ SelfParam ps loc

rnTypeParam :: TypeParam Text -> TcM (TypeParam Name)
rnTypeParam (TypeParam lname k) = TypeParam <$> checkLTypeName lname <*> pure k
rnTypeParam (TypeParamQualify dataName mStageName domName) =
  TypeParamQualify
    <$> checkLTypeName dataName
    <*> traverse checkLTypeName mStageName
    <*> checkLTypeName domName

rnTypePred :: TypePred Text -> TcM (TypePred Name)
rnTypePred = traverseTypeInTypePred rnType

checkForDuplicates :: (Ord a, Pretty a) => [Located a] -> TcM ()
checkForDuplicates names = do
  let params = buildLocMap names
  forM_ (Map.assocs params) $ \(occ, locs) ->
    when (length locs > 1) $ do
      let msg = "Name" <+> pretty occ <+> "declared at multiple locations."
      tcAddMsg $ errMsg msg locs

rnStructImplSig
  :: StructImpl Text -> TcM (Located [TypeParam Name], Type Name, [LSignature Name])
rnStructImplSig impl@StructImpl{..}
  = do
      let implTyVars = implTypeParamVars impl
      checkForDuplicates implTyVars
      setGlobalNames implTyVars $ do
        typarams <- tcWrapLoc (mapM rnTypeParam) _structImplTypeParams
        ty <- rnType _structImplType
        sigs <- tcAllowSelf $ mapM (tcWrapLoc rnFunction . _funSignature . unLocated) _structImplBody
        pure (typarams, ty, sigs)

rnProgram
  :: ([LTypeDef Name], [LStructDecl Name], [LSignature Name], [LFunction Name], [LStructImpl Name]) -> Program Text -> TcM (Program Name)
rnProgram imports program@Program{..} =
  setTopLevelNames imports program $ do
    types <- mapM (tcWrapLoc rnTypeDef) _programTypeDefs
    structs <- mapM (tcWrapLoc rnStructDecl) _programStructDecls
    defaults <- tcWrapLoc rnDefault _programDefaults
    esigs <- mapM (tcWrapLoc rnFunction) _programTopExterns
    fsigs <- mapM (tcWrapLoc rnFunction . _funSignature . unLocated) _programTopFunctions
    let extEnvs = map sigVars esigs
    let funEnvs = map sigVars fsigs
    let funsWithTypes = zipNewly _programTopFunctions funEnvs
    (ityparamss, itypes, isigss) <- unzip3 <$> mapM (rnStructImplSig . unLocated) _programStructImpls
    let ityvarss = map (map unLocated . concatMap getTyParamNames . unLocated) ityparamss
    let implEnvss = zipWith3 (\ ityvars itype isigs -> (itype , map ((_2 %~ nub . (ityvars ++)) . sigVars) isigs)) ityvarss itypes isigss
    let implsWithTypes = zipWith zipNewly (map (_structImplBody . unLocated) _programStructImpls) (map snd implEnvss)
    tcSetRnFunctions (extEnvs ++ funEnvs ++ concat (map snd implEnvss)) $ do
      funs <- zipWithM rnBody fsigs funsWithTypes
      implFuns <- zipWithM (zipWithM rnBody) isigss implsWithTypes
      let impls = zipWith Located (map location _programStructImpls) (zipWith3 StructImpl ityparamss itypes implFuns)
      return $ Program
        { _programTypeDefs = types
        , _programStructDecls = structs
        , _programTopFunctions = funs
        , _programTopExterns = esigs
        , _programImports = _programImports
        , _programStructImpls = impls
        , _programDefaults = defaults
        }
  where
    sigVars lsig = ( unLocated $ _sigName $ unLocated lsig
                   , map unLocated $ allSigTypeVars $ unLocated lsig
                   )
    rnBody sig (f, tyNames) = tcWrapLoc (rnFunctionBody sig tyNames) f
    zipNewly = zipWith (\ f (_ , tyNames) -> (f , tyNames))

rnFieldDecl :: StructFieldDecl Text -> TcM (StructFieldDecl Name)
rnFieldDecl (StructFieldDecl name ty) = StructFieldDecl name <$> rnType ty

rnStructDecl :: StructDecl Text -> TcM (StructDecl Name)
rnStructDecl StructDecl{..} = do
  sname <- checkLName _structDeclName
  let structTyVars = concatMap getTyParamNames _structDeclTypeParams
  checkForDuplicates structTyVars
  let structFieldNames = map _fieldDeclName _structDeclFields
  checkForDuplicates structFieldNames
  setGlobalNames structTyVars $ do
    tyParams <- mapM rnTypeParam _structDeclTypeParams
    fields <- mapM rnFieldDecl _structDeclFields
    return $ StructDecl {
      _structDeclName = sname,
      _structDeclIsPublic = _structDeclIsPublic,
      _structDeclTypeParams = tyParams,
      _structDeclFields = fields
    }

rnDefault :: Default Text -> TcM (Default Name)
rnDefault = traverseOf defaultFields (traverse rnType)

checkSigParam
  :: Int -> FuncParam name -> TcM (Maybe (Located name))
checkSigParam ix fp
  = case fp of
      FuncParam{..} -> pure (Just _fnParamName)
      SelfParam{..} -> tcSetLoc _fnParamLoc $ 
                       if ix == 0
                         then pure Nothing
                         else tcThrowErr $ "Self parameter in a subsequent position"

-- Verify that:
--   . The signature does not contain self parameters in subsequent positions;
--   . The signature does not declare the same parameter multiple times.
checkSigParams :: Signature Text -> TcM [Located Text]
checkSigParams sign = do
  names <- fmap catMaybes $ zipWithM checkSigParam [0 ..] $ unLocated $ _sigParameters sign
  checkForDuplicates names
  return names

rnFunction :: Signature Text -> TcM (Signature Name)
rnFunction sig = do
  fname <- checkLName $ _sigName sig
  let tyVarLocs = buildLocMap $ allSigTypeVars sig
  names <- checkSigParams sig
  forM_ (Map.assocs tyVarLocs) $ \(occ, locs) -> do
    when (occ `elem` map unLocated names) $ do
      let msg = pretty occ <+> "occurs as parameter and also as type variable."
      tcAddMsg $ warnMsg msg locs
  let tyParams = sigTypeParamVars sig
  setNames names $
    setGlobalNames tyParams $
      rnSignature fname sig

rnFunctionBody :: LSignature Name -> [Name] -> Function Text -> TcM (Function Name)
rnFunctionBody lsig tyns Function {..} = do
  let names = mapMaybe paramNameIfAny $ unLocated $ _sigParameters $ unLocated lsig
  setNamesGeneric' tcBindTypeOccName (map noLoc tyns) $
    setNamesGeneric' tcBindVarOccName names $ do
      expr' <- rnExpr _funBody
      return $ Function { _funSignature = lsig, _funBody = expr', _funIsSieve = _funIsSieve }

rnTypeDef :: TypeDef Text -> TcM (TypeDef Name)
rnTypeDef TypeDef {..} = do
  name <- tcWrapLoc checkName _tyDefName
  checkForDuplicates (_tyDefName : paramNames)
  setGlobalNames paramNames $ do
    params <- tcWrapLoc (mapM rnTypeParam) _tyDefParams
    constr <- tcWrapLoc (mapM rnTypePred) _tyDefConstraints
    ty <- rnType _tyDefType
    return $ TypeDef
      { _tyDefName = name
      , _tyDefIsPublic = _tyDefIsPublic
      , _tyDefParams = params
      , _tyDefResultKind = _tyDefResultKind
      , _tyDefConstraints = constr
      , _tyDefType = ty
      }
  where
    paramNames = foldr go [] $ unLocated _tyDefParams
    go (TypeParam name _) = (name :)
    go (TypeParamQualify tyName mStageName domName) =
      (tyName :) . maybe id (:) mStageName . (domName :)

rnExpr :: Expr Text -> TcM (Expr Name)
rnExpr (Ascription e ty) = Ascription <$> rnExpr e <*> rnType ty
rnExpr (Assign iv tgt src) = Assign iv <$> rnExpr tgt <*> rnExpr src
rnExpr (Block stmts mRes) = rnBlock stmts mRes
rnExpr (Call iv fom tyArgs args) = do
  fom' <- rnFuncOrMethod fom
  Call iv fom' <$> mapM (rnTypeArg (_fname fom')) tyArgs <*> mapM rnExpr args
rnExpr (CallOper iv name es) = do
  fname <- checkLName name
  CallOper iv fname <$> mapM rnExpr es
rnExpr (Cast e ty) = Cast <$> rnExpr e <*> rnType ty
rnExpr (DbgAssert e1 me2) = DbgAssert <$> rnExpr e1 <*> traverse rnExpr me2
rnExpr (DbgAssertEq e1 e2 me3) =
  DbgAssertEq <$> rnExpr e1 <*> rnExpr e2 <*> traverse rnExpr me3
rnExpr (ExprLoc loc e) = ExprLoc loc <$> rnExpr e
rnExpr (For occ start end e) = withName occ $ \name ->
  For name <$> rnExpr start <*> rnExpr end <*> rnExpr e
rnExpr (IfThenElse c t mf) = IfThenElse <$> rnExpr c <*> rnExpr t <*> mapM rnExpr mf
rnExpr (Index expr slice) = Index <$> rnExpr expr <*> tcWrapLoc (traverse rnExpr) slice
rnExpr (IndexStore k v) = IndexStore <$> rnExpr k <*> rnExpr v
rnExpr (Lam isf xs mty e) = do
  let names = map _lamParamName xs
  checkForDuplicates names
  setNames names $ do
    xs' <- mapM rnLamParam xs
    mty' <- traverse rnType mty
    e' <- rnExpr e
    return $ Lam isf xs' mty' e'
rnExpr (List llst) = List <$> traverse rnExpr llst
rnExpr (Lit lit) = return $ Lit lit
rnExpr (Match e cases) = Match <$> rnExpr e <*> traverse rnCase cases
rnExpr (RefArg e) = RefArg <$> rnExpr e
rnExpr (StructCtor x ts fs) = do
  x' <- checkLName x
  StructCtor x' <$> mapM (rnTypeArg x') ts <*> mapM rnFieldCtor fs
rnExpr (Select expr selector) = Select <$> rnExpr expr <*> pure selector
rnExpr Self = tcIfSelfAllowed "expression" $ return Self
rnExpr (StoreCtor kvs) = StoreCtor <$> traverse (both rnExpr) kvs
rnExpr (Tuple es) = Tuple <$> mapM rnExpr es
rnExpr (Var name) = Var <$> checkLName name
rnExpr (While cond body) = While <$> rnExpr cond <*> rnExpr body
rnExpr (WireExpr e1 e2) = WireExpr <$> rnExpr e1 <*> rnExpr e2
rnExpr (TypePredExpr p) = TypePredExpr <$> rnTypePred p
rnExpr (Trace str body) = Trace str <$> rnExpr body
rnExpr (Zip pairs e) = do
  let (xs, xss) = unzip pairs
  checkForDuplicates xs
  xss' <- mapM rnExpr xss
  withNames xs $ \ xs' ->
    Zip (zip xs' xss') <$> rnExpr e
rnExpr Hole = return Hole
rnExpr _ = tcICE "Internally used syntax construct in renamer!"

rnCase :: (Located (Pat Text), Expr Text) -> TcM (Located (Pat Name), Expr Name)
rnCase (lhs, rhs)
  = rnLHS lhs $ \ lhs' ->
    (lhs' ,) <$> rnExpr rhs

rnLHS :: Located (Pat Text) -> (Located (Pat Name) -> TcM a) -> TcM a
rnLHS (Located l pat) cont = case pat of
  LitPat n    -> cont (Located l (LitPat n))
  VarPat name -> withName (Located l name) $ cont . fmap VarPat
  WildCard    -> cont (Located l WildCard)
  
rnFuncOrMethod :: FuncOrMethod Text -> TcM (FuncOrMethod Name)
rnFuncOrMethod (Func fname) = Func <$> checkLName fname
rnFuncOrMethod (Method self fname) = Method <$> rnExpr self <*> checkLName fname

rnLamParam :: LamParam Text -> TcM (LamParam Name)
rnLamParam (LamParam name mt) = LamParam <$> checkLName name <*> traverse rnType mt

rnFieldCtor :: StructFieldCtor Text -> TcM (StructFieldCtor Name)
rnFieldCtor (StructFieldCtor i e) = StructFieldCtor i <$> rnExpr e

rnTypeArg :: Located Name -> TypeArgument Text -> TcM (TypeArgument Name)
rnTypeArg _ (TypeArg ty) = TypeArg <$> rnType ty
rnTypeArg fname (TypeArgNamedType occ ty) = do
  ty' <- rnType ty
  occName <- findFunTypeName fname occ
  return $ TypeArgNamedType occName ty'
rnTypeArg fname (TypeArgQualifiedNamedType occ dom ty) = do
  ty' <- rnType ty
  tyName <- findFunTypeName fname occ
  domName <- findFunTypeName fname dom
  return $ TypeArgQualifiedNamedType tyName domName ty'

findFunTypeName :: Located Name -> Located Text -> TcM (Located Name)
findFunTypeName fname occ = do
  typeNames <- tcGetRnFunction $ unLocated fname
  case find (\tn -> unLocated occ == nameOccName tn) typeNames of
    Just n -> return $ Located (location occ) n
    Nothing -> tcThrowErr $ "Function" <+> pretty fname
      <+> "does not have type variable" <+> pretty occ <> pretty '.'

rnBlock :: [Stmt Text] -> Maybe (Expr Text) -> TcM (Expr Name)
rnBlock statementList mRes = go statementList []
  where
    go [] stmts' = do
      mRes' <- traverse rnExpr mRes
      return $ Block (reverse stmts') mRes'
    go (stmt : stmts) stmts' = rnStmt stmt (\stmt' -> go stmts (stmt' : stmts'))

rnStmt :: Stmt Text -> (Stmt Name -> TcM a) -> TcM a
rnStmt (Expr e) cont = rnExpr e >>= cont . Expr
rnStmt (Break l) cont = cont (Break l)
rnStmt (Continue l) cont = cont (Continue l)
rnStmt (Return e) cont = rnExpr e >>= cont . Return
rnStmt (Let b (Binding mut occ mTy) e) cont = do
   ty <- traverse rnType mTy
   if b -- is recursive
     then withName occ $ \name -> do
        expr <- rnExpr e
        cont $ Let b (Binding mut name ty) expr
     else do
       expr <- rnExpr e
       withName occ $ \name ->
        cont $ Let b (Binding mut name ty) expr

rnType :: Type Text -> TcM (Type Name)
rnType (TCon con l)  = return $ TCon con l
rnType (TVar x k l)  = TVar <$> tcSetLoc l (checkTypeName x) <*> pure k <*> pure l
rnType (TApp t ts l) = TApp <$> rnType t <*> traverse rnType ts <*> pure l
rnType (TSelf l)     = tcSetLoc l $
                       tcIfSelfAllowed "type" $
                       return $ TSelf l

rnEffect :: Effect' Text Text -> TcM (Effect' Name Name)
rnEffect (Effect [] ts) = Effect [] <$> mapM rnType ts
rnEffect _ = tcICE "_effectMetaVars must be empty in effect annotations"

rnTypeWithEffect :: TypeWithEffect' Text Text -> TcM (TypeWithEffect' Name Name)
rnTypeWithEffect TweAny = return TweAny
rnTypeWithEffect (TweTuple twes) = TweTuple <$> mapM rnTypeWithEffect twes
rnTypeWithEffect (TweFun twe1 twe2 e []) = TweFun <$> rnTypeWithEffect twe1 <*> rnTypeWithEffect twe2 <*> rnEffect e <*> pure []
rnTypeWithEffect (TweFun _ _ _ _) = tcThrowErr "Constraints not yet supported in effect annotations"

rnPolyTwe :: PolymorphicTypeWithEffect Text -> TcM (PolymorphicTypeWithEffect Name)
rnPolyTwe (PolyTwe es twe) = setGlobalNames (map noLoc es) $ PolyTwe <$> mapM checkTypeName es <*> rnTypeWithEffect twe

{---------------------------------------
 -- Located versions of the functions --
 ---------------------------------------}

checkLName :: Located Text -> TcM (Located Name)
checkLName = tcWrapLoc checkName

checkLTypeName :: Located Text -> TcM (Located Name)
checkLTypeName = tcWrapLoc checkTypeName
