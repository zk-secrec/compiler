{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
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

module Core.Translate (
  programToCore,
  runTrM,
)
where

import Basic.Location
import Basic.Name
import Basic.Var
import Core.Syntax
import Core.LambdaLifting (freeVarsInCoreLet)
import Parser.Syntax
import Parser.SyntaxDump
import Support.Pretty
import Support.Unique
import Typing.StructEnv
import Typing.Typing

import Control.Lens ((<%=), both)
import Control.Lens.TH (makeLenses)
import Control.Monad.Except
import Control.Monad.RWS.Strict
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Support.UniqMap
import Control.Exception

newtype TrState = TrState
  { _supply :: Unique
  }

makeLenses ''TrState

type Bindings = ([CoreBind], Any)

type TrOutput = Bindings

data TrEnv
  = TrEnv
  { _trLoc :: Location
  , _trStructEnv :: UniqMap StructEnv
  , _trLoopDepth :: !Int
  , _trBreakOffset :: !Int
  , _trReturnVar :: Maybe Var
  }

type TrM a = ExceptT String (RWS TrEnv TrOutput TrState) a

runTrM :: Unique -> UniqMap StructEnv -> TrM a -> Either String (a, Unique)
runTrM initialUniq structEnv act = (, _supply st) <$> res
  where
    initEnv = TrEnv NoLocation structEnv 0 1 Nothing
    ~(res, st, _) = runRWS (runExceptT act) initEnv initState
    initState = TrState initialUniq

trEnterLoop :: TrM a -> TrM a
trEnterLoop = local $ \env -> env { _trLoopDepth = _trLoopDepth env + 1 }

trIncrementBreakOffset :: TrM a -> TrM a
trIncrementBreakOffset = local $ \env -> env { _trBreakOffset = _trBreakOffset env + 1 }

trSetRetVar :: Var -> TrM a -> TrM a
trSetRetVar x = local $ \env -> env { _trReturnVar = Just x }

-- throws an error
trFatal :: String -> TrM a
trFatal msg = do
  loc <- asks _trLoc
  let locMsg = render (pretty loc :: Doc ())
  throwError $ locMsg ++ ": " ++ msg

trSetLoc :: Location -> TrM a -> TrM a
trSetLoc l = local (\env -> env { _trLoc = l })

-- "listens" all bindings during translating a block and removes them from the monoid
trCollectBinds :: TrM a -> TrM (a, [CoreBind])
trCollectBinds = censor (\o -> ([], snd o)) . listens fst

-- Generates fresh variable of given type.
-- Will be mutable if generation is under by-ref argument.
trFresh :: Type TyVar -> Mutability -> TrM Var
trFresh t mut = do
  uniq <- supply <%= nextUnique
  loc <- asks _trLoc
  let name = mkName (T.pack "t") uniq loc
  let var = mkId name mut (typeToScheme t)
  return var

tellBinds :: [CoreBind] -> TrM ()
tellBinds bs = tell (bs, Any False)

tellReturns :: TrM ()
tellReturns = tell ([], Any True)

mkSimpleBind :: Var -> CoreExpr -> CoreBind
mkSimpleBind x = CoreBind False (CorePat [x])

-- saves new bindings of Core patterns to Core expressions into the monoid (3 cases)
trEmitBind :: Var -> CoreExpr -> TrM ()
trEmitBind x e = tellBinds [mkSimpleBind x e]

trEmitTupleBind :: [Var] -> CoreExpr -> TrM ()
trEmitTupleBind xs e = tellBinds [CoreBind False (CorePat xs) e]

trEmitRecBind :: Var -> CoreExpr -> TrM ()
trEmitRecBind x e = tellBinds [CoreBind True (CorePat [x]) e]

-- finds the "l-value" (if any) of a given ZKSC expression in the form of a pair of a Core variable and its offset vector
getAssignmentTargetVar :: Expr Var -> Type TyVar -> TrM (Var, [CoreOffset])
getAssignmentTargetVar e ctxType = do
  (e', _, offs) <- trGetLoadTarget e (Just ctxType)
  case e' of
    Var (Located _ x) -> return (x, offs)
    _ -> trFatal "ICE: getAssignmentTargetVar: Unsupported form of assignment."

tryGetVar :: Expr Var -> Maybe Var
tryGetVar (Var (Located _ x)) = Just x
tryGetVar (ExprLoc _ e) = tryGetVar e
tryGetVar (TypeAnnot _ e) = tryGetVar e
tryGetVar (Ascription e _) = tryGetVar e
tryGetVar _ = Nothing

trExpectTypeCtx :: Maybe (Type TyVar) -> TrM (Type TyVar)
trExpectTypeCtx Nothing = trFatal "ICE: Missing type annotation."
trExpectTypeCtx (Just t) = return t

-- extracting the component type vector and the offset vector from a given ZKSC expression
trGetLoadTarget :: Expr Var -> Maybe (Type TyVar) -> TrM (Expr Var, [Type TyVar], [CoreOffset])
trGetLoadTarget (ExprLoc l e) mt = trSetLoc l $ trGetLoadTarget e mt
trGetLoadTarget (TypeAnnot t e) _ = trGetLoadTarget e (Just t)
trGetLoadTarget (Ascription e t) _ = trGetLoadTarget e (Just t)
trGetLoadTarget var@(Var (Located _ x)) _ = return (var, [ty], [])
  where TForAll _ _ ty = idType x
trGetLoadTarget (RefArg e) mt = trGetLoadTarget e mt
trGetLoadTarget (Select e s) mt = do
  (e', ts, is) <- trGetLoadTarget e Nothing
  t <- trExpectTypeCtx mt
  off <- case s of
    SelectIndex j -> return $ COffTuple j
    SelectField fname -> assert (not (null ts)) $ do
      j <- trFieldToIndex (last ts) fname
      return $ COffStruct j
  return (e', ts ++ [t], is ++ [off])
trGetLoadTarget (Index e (Located _ slice)) mt = do
  (e', ts, is) <- trGetLoadTarget e Nothing
  t <- trExpectTypeCtx mt
  slice' <- traverse exprToCore' slice
  return (e', ts ++ [t], is ++ [COffDynamic  slice'])
trGetLoadTarget (IndexStore e i) mt = do
  (e', ts, is) <- trGetLoadTarget e Nothing
  t <- trExpectTypeCtx mt
  i' <- exprToCore' i
  return (e', ts ++ [t], is ++ [COffKey i'])
trGetLoadTarget e mt = do
  t <- trExpectTypeCtx mt
  return (e, [t], [])

isRefArg :: Expr Var -> Bool
isRefArg (RefArg _) = True
isRefArg (ExprLoc _ e) = isRefArg e
isRefArg (TypeAnnot _ e) = isRefArg e
isRefArg (Ascription e _) = isRefArg e
isRefArg _ = False

-- finding out the Core load statement corresponding to a given index or select
-- expression and storing it in the monoid
trLoadToCore :: Expr Var -> Var -> TrM ()
trLoadToCore e r0 = do
  let TForAll _ _ t = idType r0
  (e', ts, is) <- trGetLoadTarget e (Just t)
  let refArg = isRefArg e
  let loadCtor = if refArg then CeRef else CeLoad
  case tryGetVar e' of
    Just x -> trEmitBind r0 (loadCtor x is)
    Nothing -> do
      when refArg $
        trFatal "ICE: trLoadToCore: lvalue argument is being passed by reference."
      x <- trFresh (head ts) Immutable
      exprToCore e' x
      trEmitBind r0 (CeLoad x is)

mkScalar :: Expr Var
mkScalar
  = TypeAnnot mkTypeUnit (Lit ConstUnit)

typeCtx :: Expr Var -> TrM (Type TyVar)
typeCtx (Var x) = let TForAll _ _ t = idType (unLocated x) in return t
typeCtx (ExprLoc l e) = trSetLoc l $ typeCtx e
typeCtx (TypeAnnot t _) = return t
typeCtx _ = trFatal "ICE: Missing type context."

-- finding the Core variable corresponding to a given ZKSC expression;
-- triggers exprToCore for establishing necessary bindings for subexpressions
-- Will generate fresh variable by expression is pass-by-ref.
exprToCore' :: Expr Var -> TrM Var
exprToCore' e = do
  t <- typeCtx e
  let mut = if isRefArg e then Mutable else Immutable
  r <- trFresh t mut
  exprToCore e r
  return r

-- transforms a given ZKSC expression to a Core let expression
exprToLet :: Expr Var -> TrM CoreLet
exprToLet e = do
  (r, bs) <- trCollectBinds $ exprToCore' e
  return $ CoreLet bs [r]

isLengthBuiltin :: Var -> Bool
isLengthBuiltin x = matchBuiltin (varName x) BuiltinLength

tyArgToType :: TypeArgument a -> TrM (Type a)
tyArgToType = \case
  TypeArg t -> return t
  _ -> trFatal "ICE: Unexpected named type argument. Should have been resolved during type checking."

callToCore :: IsVectorized -> Var -> [TypeArgument Var] -> [Expr Var] -> Var -> TrM ()
callToCore _ x targs [e] r0
  | isLengthBuiltin x
  , Right (Located _ (Just y)) <- getLValueTarget e
  , idIsMutable y = do
    -- We special case length construct so it would pass mutable argumement by
    -- reference despite the fact that the function takes immutable argument.
    -- Otherwise backend would create a copy during mut -> immut conversion.
    ts <- mapM tyArgToType targs
    t <- typeCtx e
    tmp <- trFresh t Mutable
    trLoadToCore (RefArg e) tmp
    l <- asks _trLoc
    trEmitBind r0 (CeCall NotVectorized x ts [tmp] l)
callToCore iv x targs es r0 = do
  rs <- mapM exprToCore' es
  ts <- mapM tyArgToType targs
  l <- asks _trLoc
  trEmitBind r0 (CeCall iv x ts rs l)

litcaseToCore'
  :: (Located (Pat Var), Expr Var) -> TrM (Integer, Var)
litcaseToCore' (lhs, rhs)
  = let LitPat n = unLocated lhs in
    (n ,) <$> exprToCore' rhs

emitCase
  :: ((Integer, Var), [CoreBind]) -> (Integer, CoreLet)
emitCase ((n, x), bs)
  = (n, CoreLet bs [x])

emitDefCase
  :: (Var, [CoreBind]) -> CoreLet
emitDefCase (x, bs)
  = CoreLet bs [x]

defcaseToCore'
  :: Var -> (Located (Pat Var), Expr Var) -> TrM Var
defcaseToCore' r (lhs, rhs)
  = do
      bindVarWith r (unLocated lhs)
      exprToCore' rhs

bindVarWith
  :: Var -> Pat Var -> TrM ()
bindVarWith r lhs
  = case lhs of
      VarPat v
        -> trEmitBind v (CeVar r)
      _ -> return ()

-- collects the Core bindings corresponding to all subexpressions of a given ZKSC expression into the monoid (the target of the whole expression is given as the second parameter)
exprToCore :: Expr Var -> Var -> TrM ()
exprToCore (Ascription e _) r0 = exprToCore e r0
exprToCore (IfThenElse e1 e2 me3) r0 = do
  r1 <- exprToCore' e1
  let defaultExpr = mkScalar
  let e3 = fromMaybe defaultExpr me3
  (rt, bt) <- trCollectBinds $ exprToCore' e2
  (rf, bf) <- trCollectBinds $ exprToCore' e3
  let exprt = CoreLet bt [rt]
  let exprf = CoreLet bf [rf]
  trEmitBind r0 (CeIfThenElse r1 exprt exprf)
exprToCore (TypeIf p e2 e3) r0 = do
  (rt, bt) <- trCollectBinds $ exprToCore' e2
  (rf, bf) <- trCollectBinds $ exprToCore' e3
  let exprt = CoreLet bt [rt]
  let exprf = CoreLet bf [rf]
  trEmitBind r0 (CeTypeIf p exprt exprf)
exprToCore (Match e cases) r0 = do
  let TForAll _ _ t0 = idType r0
  r1 <- exprToCore' e
  let (litcases , defcases) = span (isLitPat . unLocated . fst) cases
  let mdefcase = listToMaybe defcases
  (ns, cs) <- unzip <$> traverse (fmap emitCase . trCollectBinds . litcaseToCore') litcases
  c <- maybe (trFatal "ICE: Match expression without default case") (fmap emitDefCase . trCollectBinds . defcaseToCore' r1) mdefcase
  uniq <- supply <%= nextUnique
  -- the union of free variables in all cases
  let freeVars0 = map snd $ toListUM $ unionsUM $ map (freeVarsInCoreLet uniq) (c : cs)
  -- remove variables with function type
  let freeVars = filter (not . isFuncType . _typeSchemeType . idType) freeVars0
  let funTy = mkFunArgs (if null freeVars then [mkTypeUnit] else map (_typeSchemeType.idType) freeVars) t0
  emitLam <- return $ \ c -> do
    x <- trFresh funTy Immutable
    if null freeVars
      then do
        unitArg <- trFresh mkTypeUnit Immutable
        trEmitBind x (CeLam IsSieveFn [unitArg] c)
      else trEmitBind x (CeLam IsSieveFn freeVars c)
    return x
  xs <- traverse emitLam cs
  x <- emitLam c
  trEmitBind r0 (CeMatch r1 (zip ns xs) x freeVars)
exprToCore (Tuple es) r0 = do
  rs <- mapM exprToCore' es
  trEmitBind r0 (CeTuple rs)
exprToCore (Call iv (Func x) targs es) r0 = callToCore iv (unLocated x) targs es r0
exprToCore (Assign _iv e1 e2) r0 = do
  let TForAll _ _ t = idType r0
  (x, offs) <- getAssignmentTargetVar e1 t
  r <- exprToCore' e2
  trEmitBind r0 (CeStore x offs r) -- TODO: Should the vectorization flag be in action somehow?
exprToCore (Block stmts (Just e)) r0 = do
  mapM_ stmtToCore stmts
  exprToCore e r0
exprToCore (Cast e t) r0 = do
  r <- exprToCore' e
  trEmitBind r0 (CeCast r t)
exprToCore (DbgAssert e1 me2) r0 = do
  l <- asks _trLoc
  r1 <- exprToCore' e1
  mlet <- traverse exprToLet me2
  trEmitBind r0 (CeDbgAssert r1 l mlet)
exprToCore (DbgAssertEq e1 e2 me3) r0 = do
  l <- asks _trLoc
  r1 <- exprToCore' e1
  r2 <- exprToCore' e2
  mlet <- traverse exprToLet me3
  trEmitBind r0 (CeDbgAssertEq r1 r2 l mlet)
exprToCore (ExprLoc l e) r0 = trSetLoc l $ exprToCore e r0
exprToCore (For lx e1 e2 e3) r0
  | isUnitType t = forStmtToCore x e1 e2 e3 r0
  | isListType t = forExprToCore False x e1 e2 e3 r0
  | otherwise = trFatal $ "ICE: Unsupported result type of a for-loop (" ++ tmsg ++ ")"
  where
    x = unLocated lx
    TForAll _ _ t = idType r0
    tmsg = render (pretty t :: Doc ())
exprToCore (Zip pairs e) r0 = zipExprToCore xs' xss e r0
  where
    (xs, xss) = unzip pairs
    xs' = map unLocated xs
exprToCore index@Index{} r0 = trLoadToCore index r0
exprToCore sel@Select{} r0 = trLoadToCore sel r0
exprToCore index@IndexStore{} r0 = trLoadToCore index r0
exprToCore ref@RefArg{} r0 = trLoadToCore ref r0
exprToCore (Lam isf ps _ e) r0 = do
  let xs = [x | LamParam (Located _ x) _ <- ps]
  lt <- exprToLet e
  trEmitBind r0 (CeLam isf xs lt)
exprToCore (List elems) r0 = do
  elems' <- traverse exprToCore' elems
  trEmitBind r0 (CeList elems')
exprToCore (Lit c) r0 = trEmitBind r0 (CeLit c)
exprToCore (StoreCtor kvs) r0 = do
  xys <- mapM (both exprToCore') kvs
  trEmitBind r0 (CeStoreCtor xys)
exprToCore (StructCtor name targs fs) r0 = do
  ts <- mapM tyArgToType targs
  -- NOTE: We assume that type checker has already ordered fields appropriately.
  rs <- mapM (\(StructFieldCtor _ e) -> exprToCore' e) fs
  trEmitBind r0 (CeStructCtor (unLocated name) ts rs)
exprToCore (TypeAnnot _ e) r0 = exprToCore e r0
exprToCore (Var (Located _ x)) r0
  | x == r0 = return ()
  | idIsMutable x = trEmitBind r0 (CeLoad x [])
  | otherwise = trEmitBind r0 (CeVar x)
exprToCore (While e1 e2) r0 = trEnterLoop $ do
  -- while e1 e2 --> loop { if (e1) { e2 } else { break; } }
  -- e1 may contain break or continue expression.
  -- this means that break and continue have to break out of generated loop as well
  (r1, bs) <- trIncrementBreakOffset $ trCollectBinds $ exprToCore' e1
  trueBranch <- exprToLet e2
  let CoreLet _ [x] = trueBranch
  let TForAll _ _ unitTy = idType x
  r2 <- trFresh unitTy Immutable
  r2' <- trFresh unitTy Immutable
  breakEpxr <- trBreak
  let falseBranch = CoreLet [mkSimpleBind r2 breakEpxr, mkSimpleBind r2' (CeLit ConstUnit)] [r2']
  let ifteExpr = CeIfThenElse r1 trueBranch falseBranch
  r3 <- trFresh unitTy Immutable
  let loopBody = CoreLet (bs ++ [mkSimpleBind r3 ifteExpr]) [r3]
  trEmitTupleBind [r0] $ CeLoop $ CoreForever loopBody
exprToCore (WireExpr shape e) r0 = do
  shape' <- exprToCore' shape
  (r, bs) <- trCollectBinds $ exprToCore' e
  trEmitBind r0 (CeWire shape' (CoreLet bs [r]))
exprToCore (Trace (Located _ str) e) r0 = do
  l <- asks _trLoc
  lt <- exprToLet e
  trEmitBind r0 (CeTrace l str lt)
exprToCore (TypeToExpr t) r0 = trEmitBind r0 (CeTypeToExpr t)
exprToCore (Block _ Nothing) _ = trFatal "ICE: block with no body."
exprToCore CallOper{} _ = trFatal "ICE: CallOper left from type checking."
exprToCore TypePredExpr{} _ = trFatal "ICE: Type predicate expressions not yet supported."
exprToCore Hole _ = trFatal "ICE: Hole remains in program"
exprToCore (Call _ (Method _ _) _ _) _ = trFatal "ICE: Method calls not yet supported."
exprToCore Self _ = trFatal "ICE: Self parameters not yet supported."

trBreak :: TrM CoreExpr
trBreak = CeBreak <$> asks _trBreakOffset

trContinue :: TrM CoreExpr
trContinue = CeContinue <$> asks _trBreakOffset

recExprToCore :: Expr Var -> Var -> TrM ()
recExprToCore (ExprLoc l e) r0 = trSetLoc l $ recExprToCore e r0
recExprToCore (TypeAnnot _ e) r0 = recExprToCore e r0
recExprToCore (For lx e1 e2 e3) r0
  | isListType t = forExprToCore True x e1 e2 e3 r0
  | otherwise = trFatal $ "ICE: Unsupported result type of a recursive for-loop (" ++ tmsg ++ ")"
  where
    x = unLocated lx
    TForAll _ _ t = idType r0
    tmsg = render (pretty t :: Doc ())
recExprToCore e _ = trFatal $ "ICE: Unsupported recursive expression (" ++ render (dumpExpr e) ++ ")"

-- finds the structenv corresponding to a given type variable
trFindStructVar :: TyVar -> TrM StructEnv
trFindStructVar x = do
  structs <- asks _trStructEnv
  case lookupUM x structs of
    Nothing -> trFatal "Core.Translate: Polymorphic structs are not yet supported."
    Just senv -> return senv

-- finds the structenv corresponding to the type variable at the head position of a given type expression
trFindStructEnv :: Type TyVar -> TrM StructEnv
trFindStructEnv (TVar x _ l) = trSetLoc l $ trFindStructVar x
trFindStructEnv t@(TQualify u _ _) = trSetLoc (location t) $ trFindStructEnv u
trFindStructEnv (TApp (TVar x _ _) _ l) = trSetLoc l $ trFindStructVar x
trFindStructEnv t = trFatal $ "Core.Translate: ICE: Unexpected type. " ++ render (pretty t)

-- translates a given field name of a given struct type to an index
trFieldToIndex :: Type TyVar -> T.Text -> TrM Int
trFieldToIndex ty fname = do
  StructEnv{..} <- trFindStructEnv ty
  case M.lookup fname _structFields of
    Nothing -> trFatal "ICE: Core.Translate: Unknown field name."
    Just StructFieldInfo{..} -> return _fieldPos

zipExprToCore :: [Var] -> [Expr Var] -> Expr Var -> Var -> TrM ()
zipExprToCore xs xss e r0 = do
  rs <- mapM exprToCore' xss
  (r, b) <- trCollectBinds $ trEnterLoop $ exprToCore' e
  let loopBody = CoreLet b [r]
  let typeSchemeToType (TForAll _ _ t) = t
  let idToType = typeSchemeToType . idType
  let t = mkFunArgs (map idToType xs) (idToType r)
  f <- trFresh t Immutable
  trEmitBind f $ CeLam IsSieveFn xs loopBody -- TODO: should we also support NotSieveFn for zip expressions?
  trEmitBind r0 $ CeCall IsVectorized f [] rs NoLocation

forExprToCore :: Bool -> Var -> Expr Var -> Expr Var -> Expr Var -> Var -> TrM ()
forExprToCore recursive x e1 e2 e3 r0 = do
  r1 <- exprToCore' e1
  r2 <- exprToCore' e2
  (r3, bs) <- trCollectBinds $ trEnterLoop $ exprToCore' e3
  let loopBody = CoreLet bs [r3]
  (if recursive then trEmitRecBind else trEmitBind) r0 $ CeLoop $ CoreForExpr x r1 r2 loopBody

forStmtToCore :: Var -> Expr Var -> Expr Var -> Expr Var -> Var -> TrM ()
forStmtToCore x e1 e2 e3 r0 = do
  r1 <- exprToCore' e1
  r2 <- exprToCore' e2
  (r3, bs) <- trCollectBinds $ trEnterLoop $ exprToCore' e3
  let loopBody = CoreLet bs [r3]
  trEmitTupleBind [r0] $ CeLoop $ CoreForRange x r1 r2 loopBody

-- collects the Core bindings corresponding to all subunits of a given ZKSC statement into the monoid (the target of the whole expression is given as the second parameter)
stmtToCore :: Stmt Var -> TrM ()
stmtToCore (Expr e) = void (exprToCore' e)
stmtToCore (Let recursive (Binding _ (Located _ x) _) e2) =
  (if recursive then recExprToCore else exprToCore) e2 x
stmtToCore (Break _) = do
  r0 <- trFreshImmutUnitVar
  trEmitBind r0 =<< trBreak
stmtToCore (Continue _) = do
  r0 <- trFreshImmutUnitVar
  trEmitBind r0 =<< trContinue
stmtToCore (Return e) = do
  tellReturns
  retVar <- asks _trReturnVar >>= \case
    Nothing -> trFatal "ICE: Missing return variable"
    Just x -> return x
  r <- exprToCore' e
  r0 <- trFreshImmutUnitVar
  trEmitBind r0 (CeStore retVar [] r)
  loopDepth <- asks _trLoopDepth
  r1 <- trFreshImmutUnitVar
  trEmitBind r1 (CeBreak (loopDepth + 1))

trFreshImmutUnitVar :: TrM Var
trFreshImmutUnitVar = trFresh mkTypeUnit Immutable

implToCore :: TypedStructImpl -> TrM CoreStructImpl
implToCore (TypedStructImpl t fs) = CoreStructImpl t <$> mapM functionToCore fs

programToCore :: TypedProgram -> TrM CoreProgram
programToCore (TypedProgram exts funcs impls _ _ _) =
  CoreProgram <$> mapM externToCore exts <*> mapM (traverse functionToCore) funcs <*> mapM implToCore impls

trFuncResult :: Type Var -> Int -> TrM (Type Var)
trFuncResult _  n | n < 0 = trFatal "ICE: trFuncResult: Negative split position."
trFuncResult ty 0 = return ty
trFuncResult ty n = case ty of
  TQualify (TFun _ t2) _ _ -> trFuncResult t2 (n - 1)
  TFun _ t2 -> trFuncResult t2 (n - 1)
  _ -> trFatal "ICE: trFuncResult: Expecting more function arguments."

externToCore :: TypedTopExtern -> TrM CoreTopExtern
externToCore (TypedTopExtern x _ xs _) = 
  return (CoreTopExtern x xs)

functionToCore :: TypedTopFunction -> TrM CoreTopFunction
functionToCore (TypedTopFunction x _ xs e _ isf) = do
  let TForAll _ _ funTy = idType x
  resTy <- trFuncResult funTy (if null xs then 1 else length xs) -- empty argument vector means one parameter of unit type
  r0 <- trFresh resTy Immutable
  earlyRetVar <- trFresh resTy Mutable
  ((), (bs, hasEarlyReturn)) <- trSetRetVar earlyRetVar $ censor (const ([], Any False)) $ listen $ exprToCore e r0
  if getAny hasEarlyReturn
    then do
      let stmt1 = mkSimpleBind earlyRetVar CeBot
      ~[t1, t2, t3] <- replicateM 3 $ trFreshImmutUnitVar
      let storeBind = mkSimpleBind t1 (CeStore earlyRetVar [] r0)
      let breakBind = mkSimpleBind t2 (CeBreak 1)
      let loopBody = CoreLet (bs ++ [storeBind, breakBind]) [t2]
      let stmt2 = mkSimpleBind t3 (CeLoop (CoreForever loopBody))
      r2 <- trFresh resTy Immutable
      let stmt3 = mkSimpleBind r2 (CeLoad earlyRetVar [])
      return $ CoreTopFunction x xs (CoreLet [stmt1, stmt2, stmt3] [r2]) isf NotLambda
    else return $ CoreTopFunction x xs (CoreLet bs [r0]) isf NotLambda
