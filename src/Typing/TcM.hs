{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
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

module Typing.TcM (
  Env(..),
  TcM,

  --
  runTcM,
  tcCatchMsgs,

  -- verbosity
  tcGetVerbose,
  tcSetVerbose,

  -- environment
  setEnv,
  getEnv,
  getsEnv,
  updEnv,
  tcTyEnv,
  tcVarRnEnv,
  tcTypeRnEnv,
  tcMsgs,
  tcSupply,
  tcStructEnv,

  -- exceptions
  TcException,
  tcFail,
  tcTry,
  tcThrowIfErrs,

  -- messages
  tcSetMsgVar,
  tcGetMsgVar,
  tcGetMsgs,
  tcCheckIfErrs,
  tcAddMsg,
  tcAddErr,
  tcAddWarn,
  tcAddFatal,
  tcFatal,
  tcICE,
  tcThrowErr,
  tcDebugPrint,

  -- locations
  tcSetLoc,
  tcGetLoc,
  tcWithLoc,
  tcWrapLoc,
  tcWrapLoc',
  tcWrapSndLoc,
  tcWrapFstLoc,

  -- unique supply
  tcFreshUniq,

  -- names
  tcFreshName,
  tcFreshMetaTyVar,
  tcFreshMetaTy,
  tcFreshUnqualifiedTy,
  tcFreshDomainTy,
  tcFreshStageTy,
  tcFreshQualifiedTy,
  tcFreshQualifiedTy',
  lookupVar,
  findVar,
  findId,
  tcSetVar,
  tcSetVars,
  tcSetVarSet,
  tcBindVarOccName,
  tcBindTypeOccName,
  tcLookupVarOccName,
  tcLookupTypeOccName,
  tcSetType,
  tcLookupType,
  tcFindType,
  tcLookupTyVar,
  tcFindTyVar,

  -- structs
  tcSetStruct,
  tcLookupStruct,
  tcFindStruct,
  tcIsStruct,
  tcGetStructsEnv,

  -- functions
  tcSetRnFunctions,
  tcGetRnFunction,
  tcSetTopFunParams,
  tcGetTopFunParams,

  -- references
  newRef,
  readRef,
  writeRef,

  -- constraints
  tcAddWanted,
  tcCollectWanted,
  tcTakeConstraints,
  tcAddSubConstr,
  tcAddImplication,
  tcAndWanted,
  tcAddQualifyConstr,
  tcUnifyTypes,

  --
  tcGetBranchDomain,
  tcSetBranchDomain,

  -- loops
  tcSetInForStmt,
  tcLeaveForStmt,
  tcIsInForStmt,

  -- return type
  tcGetReturnType,
  tcSetReturnType,

  -- substitutions
  tcTakeSubs,
  tcAddSub,
  tcSubType,

  -- unsolved variables
  tcAddUnsolved,
  tcTakeUnsolved,
  tcRemoveUnsolved,

  -- Levels
  tcGetLevel,
  tcWithLevel,
  tcWithNextLevel,

  -- Type synonym occurrences
  tcAddSynonymOccur,
  tcSynonymOccurs,

  -- Information about builtins
  tcSetDocBuiltins,
  tcDocBuiltins,

  -- Self
  tcAllowSelf,
  tcIfSelfAllowed,
  tcSetSelfType,
  tcGetSelfType
) where

import Basic.Location
import Basic.Message
import Basic.Name
import Basic.Var
import Parser.Syntax (ParamPassingStyle)
import Support.Bag
import Support.Pretty
import Support.UniqMap
import Support.Unique
import Typing.Constraints
import Typing.Kind
import Typing.StructEnv
import Typing.Type

import Control.Exception (Exception, throwIO, try)
import Control.Lens.Setter (set, over, (%~), (.~), (?~))
import Control.Lens.TH (makeLensesFor)
import Control.Monad (unless, when)
import Control.Monad.IO.Class (MonadIO(..), liftIO)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Data.IORef.Extra (writeIORef')
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Typeable (Typeable)
import GHC.Stack (HasCallStack, prettyCallStack, callStack)
import qualified Control.Monad.Fail as Fail
import qualified Data.Map as M
import System.IO (hPutStrLn, stderr)
import qualified Data.Text as T

{------------------
 -- Environments --
 ------------------}

type SubVar = IORef SubVarInfo

data SubVarInfo
  = SubVarRoot Var
  | SubVarLink (Type SubVar)

type SubVarMap = UniqMap SubVar

data Env = Env
  { _supply :: IORef Unique
  , _tcLoc :: Location
  , _tcVarRnEnv :: M.Map Text Name
  , _tcTypeRnEnv :: M.Map Text Name
  , _tcTyEnv :: UniqMap Var
  , _tcTypeDefEnv :: UniqMap (Kind, TypeScheme TyVar)
  , _tcStructEnv :: IORef (UniqMap StructEnv)
  , _tcSynonymOccurs :: IORef (UniqMap Location)
  , _tcTopFunParams :: UniqMap [ParamPassingStyle]
  , _tcFunRnEnv :: UniqMap [Name]
  , _tcSubs :: IORef SubVarMap
  , _tcUnsolved :: IORef (UniqMap MetaTyVar)
  , _tcConstr :: IORef WantedConstraints
  , _tcMsgs :: IORef (Bag Message)
  , _tcInForStmt :: Bool
  , _tcLevel :: Level
  , _tcSelfType :: Maybe (Type TyVar)
  , _tcSelf :: Bool
  , _tcReturnType :: Maybe (Type TyVar)
  , _tcBranchDomain :: Maybe (DomainType TyVar)
  , _tcDocBuiltins :: IORef [(T.Text, BuiltinInfo, TypeScheme TyVar)]
  , _verbose :: Bool
  }

makeLensesFor
  [ ("_tcLoc", "tcLoc")
  , ("_tcVarRnEnv", "tcVarRnEnv")
  , ("_tcTypeRnEnv", "tcTypeRnEnv")
  , ("_tcTyEnv", "tcTyEnv")
  , ("_tcTypeDefEnv", "tcTypeDefEnv")
  , ("_tcTopFunParams", "tcTopFunParams")
  , ("_tcFunRnEnv", "tcFunRnEnv")
  , ("_tcMsgs", "tcMsgs")
  , ("_tcInForStmt", "tcInForStmt")
  , ("_tcLevel", "tcLevel")
  , ("_tcReturnType", "tcReturnType")
  , ("_tcBranchDomain", "tcBranchDomain")
  , ("_verbose", "verbose")
  , ("_tcConstr", "tcConstr")
  , ("_supply", "tcSupply")
  , ("_tcStructEnv", "tcStructEnv")
  , ("_tcSynonymOccurs", "tcSynonymOccurs")
  , ("_tcDocBuiltins", "tcDocBuiltins")
  , ("_tcSelf", "tcSelf")
  , ("_tcSelfType", "tcSelfType")
  ]
  ''Env

mkEnv :: IO Env
mkEnv = do
  supplyRef <- newIORef (mkUnique 0)
  msgsRef <- newIORef emptyBag
  constrRef <- newIORef emptyWanted
  unsolvedRef <- newIORef emptyUM
  subsRef <- newIORef emptyUM
  structEnvRef <- newIORef emptyUM
  synonymOccursRef <- newIORef emptyUM
  docBuiltinsRef <- newIORef []
  return Env
    { _supply = supplyRef
    , _tcLoc = NoLocation
    , _tcVarRnEnv = M.empty
    , _tcTypeRnEnv = M.empty
    , _tcTyEnv = emptyUM
    , _tcTypeDefEnv = emptyUM
    , _tcSynonymOccurs = synonymOccursRef
    , _tcStructEnv = structEnvRef
    , _tcTopFunParams = emptyUM
    , _tcFunRnEnv = emptyUM
    , _tcUnsolved = unsolvedRef
    , _tcSubs = subsRef
    , _tcConstr = constrRef
    , _tcMsgs = msgsRef
    , _tcInForStmt = False
    , _tcLevel = 0
    , _tcSelf = False
    , _tcSelfType = Nothing
    , _tcReturnType = Nothing
    , _tcBranchDomain = Nothing
    , _tcDocBuiltins = docBuiltinsRef
    , _verbose = False
    }

tcGetVerbose :: TcM Bool
tcGetVerbose = getsEnv _verbose

tcSetVerbose :: Bool -> TcM a -> TcM a
tcSetVerbose b = updEnv $ set verbose b

{--------------------------------------
 -- Type checking and renaming monad --
 --------------------------------------}

newtype TcM a = TcM {
    unTcM :: Env -> IO a
  }

instance Fail.MonadFail TcM where
  fail = tcThrowErr . pretty

runUnsafeTcM :: TcM a -> IO (a, Env)
runUnsafeTcM (TcM act) = do
  env <- mkEnv
  (, env) <$> act env

runTcM :: TcM a -> IO (Maybe a, Env)
runTcM act = runUnsafeTcM $ do
  res <- tcTry act
  case res of
    Left _ -> return Nothing
    Right x -> return $ Just x

tcCatchMsgs :: TcM a -> TcM (Bag Message, Maybe a)
tcCatchMsgs act = do
  var <- newRef emptyBag
  res <- tcTry $ tcSetMsgVar var act
  msgs <- readRef var
  case res of
    Left _ -> return (msgs, Nothing)
    Right x -> return (msgs, Just x)

-- Executes the given action and throws if the action produces any errors.
-- if the inner action throws errors, we throw error too. Messages are never lost.
-- This is useful if we have a process than raises errors but continues anyways, but
-- we don't want to use the produced result because it could be in invalid state.
tcThrowIfErrs :: TcM a -> TcM a
tcThrowIfErrs act = do
  var <- newRef emptyBag
  x <- tcTry $ tcSetMsgVar var act
  msgs <- readRef var
  tcAddMsgs msgs
  case x of
    Left _ -> tcFail
    Right x' | hasErrMsg msgs -> tcFail
             | otherwise -> return x'

tcCheckIfErrs :: TcM a -> TcM (Bool, a)
tcCheckIfErrs act = do
  var <- newRef emptyBag
  x <- tcSetMsgVar var act
  msgs <- readRef var
  tcAddMsgs msgs
  return (hasErrMsg msgs, x)

{-----------------------------
 -- Various class instances --
 -----------------------------}

instance Functor TcM where
  {-# INLINE fmap #-}
  fmap = mapTcM

instance Monad TcM where
  {-# INLINE (>>=) #-}
  (>>=) = bindTcM

  {-# INLINE (>>) #-}
  (>>) = thenTcM

  {-# INLINE return #-}
  return = returnTcM

instance Applicative TcM where
  {-# INLINE pure #-}
  pure = returnTcM

  {-# INLINE (<*>) #-}
  (<*>) = appTcM

instance MonadIO TcM where
  {-# INLINE liftIO #-}
  liftIO io = TcM $ const io

mapTcM :: (a -> b) -> TcM a -> TcM b
{-# INLINE mapTcM #-}
mapTcM f (TcM m) = TcM $ \env -> fmap f (m env)

bindTcM :: TcM a -> (a -> TcM b) -> TcM b
{-# INLINE bindTcM #-}
bindTcM (TcM act) k = TcM $ \env -> act env >>= \x -> unTcM (k x) env

thenTcM :: TcM a -> TcM b -> TcM b
{-# INLINE thenTcM #-}
thenTcM (TcM act) m = TcM $ \env -> act env >> unTcM m env

returnTcM :: a -> TcM a
{-# INLINE returnTcM #-}
returnTcM x = TcM $ \_env -> return x

appTcM :: TcM (a -> b) -> TcM a -> TcM b
{-# INLINE appTcM #-}
appTcM (TcM fact) (TcM xact) = TcM $ \env -> fact env <*> xact env

{------------------------
 -- Exception handling --
 ------------------------}

data TcException = TcException
  deriving (Show, Typeable)

instance Exception TcException

tcFail :: TcM a
tcFail = TcM $ \_env -> throwIO TcException

tcTry :: TcM a -> TcM (Either TcException a)
tcTry (TcM act) = TcM $ \env -> try (act env)

{--------------
 -- Messages --
 --------------}

tcSetMsgVar :: IORef (Bag Message) -> TcM a -> TcM a
tcSetMsgVar var = updEnv $ set tcMsgs var

tcGetMsgVar :: TcM (IORef (Bag Message))
tcGetMsgVar = getsEnv _tcMsgs

tcGetMsgs :: TcM (Bag Message)
tcGetMsgs = do
  var <- tcGetMsgVar
  readRef var

tcAddMsg :: Message -> TcM ()
tcAddMsg msg = do
  var <- tcGetMsgVar
  modifyRef var (`snocBag` msg)

tcAddMsgs :: Messages -> TcM ()
tcAddMsgs msgs = do
  var <- tcGetMsgVar
  modifyRef var (msgs `unionBags`)

tcAddErr :: Doc () -> TcM ()
tcAddErr msg = do
  loc <- tcGetLoc
  tcAddMsg (errMsg msg [loc])

tcThrowErr :: Doc () -> TcM a
tcThrowErr msg = do
  tcAddErr msg
  tcFail

tcAddWarn :: Doc () -> TcM ()
tcAddWarn msg = do
  loc <- tcGetLoc
  tcAddMsg (warnMsg msg [loc])

tcAddFatal :: Doc () -> TcM ()
tcAddFatal msg = do
  loc <- tcGetLoc
  tcAddMsg (fatalMsg msg [loc])

tcDebugPrint :: Doc () -> TcM ()
tcDebugPrint doc = do
  v <- tcGetVerbose
  when v $
    liftIO $ hPutStrLn stderr (render doc)

{----------------
 -- References --
 ----------------}

newRef :: a -> TcM (IORef a)
newRef x = liftIO (newIORef x)

{-# INLINE readRef #-}
readRef :: IORef a -> TcM a
readRef ref = liftIO (readIORef ref)

{-# INLINE writeRef #-}
writeRef :: IORef a -> a -> TcM ()
writeRef ref x = liftIO (writeIORef' ref x)

{-# INLINE modifyRef #-}
modifyRef :: IORef a -> (a -> a) -> TcM ()
modifyRef ref f = ref `seq` liftIO (modifyIORef' ref f)

{------------------------
 -- Environment access --
 ------------------------}

getEnv :: TcM Env
getEnv = TcM return

getsEnv :: (Env -> a) -> TcM a
getsEnv f = TcM (return . f)

setEnv :: Env -> TcM a -> TcM a
setEnv env (TcM act) = TcM $ \_ -> act env

updEnv :: (Env -> Env) -> TcM a -> TcM a
updEnv f (TcM act) = TcM $ \env -> act (f env)

{-------------------------
 -- Location management --
 -------------------------}

tcSetLoc :: Location -> TcM a -> TcM a
tcSetLoc newLoc act = case newLoc of
  NoLocation -> act
  _ -> updEnv (set tcLoc newLoc) act

tcFatal :: Doc () -> TcM a
tcFatal msg = tcAddFatal msg >> tcFail

tcICE :: HasCallStack => Doc () -> TcM a
tcICE msg = tcAddFatal ("ICE:" <+> msg $$ indent 2 (pretty (prettyCallStack callStack))) >> tcFail

tcWithLoc :: (a -> TcM b) -> Located a -> TcM b
tcWithLoc k (Located loc x) = tcSetLoc loc (k x)

tcWrapLoc :: (a -> TcM b) -> Located a -> TcM (Located b)
tcWrapLoc k (Located loc x) = tcSetLoc loc (Located loc <$> k x)

tcWrapLoc' :: (HasLocation a) => (a -> TcM b) -> a -> TcM b
tcWrapLoc' k x = tcSetLoc (location x) (k x)

tcWrapSndLoc :: (a -> TcM (b, c)) -> Located a -> TcM (b, Located c)
tcWrapSndLoc k lx = do
  Located loc (x, y) <- tcWrapLoc k lx
  return (x, Located loc y)

tcWrapFstLoc :: (a -> TcM (b, c)) -> Located a -> TcM (Located b, c)
tcWrapFstLoc k lx = do
  Located loc (x, y) <- tcWrapLoc k lx
  return (Located loc x, y)

tcGetLoc :: TcM Location
tcGetLoc = getsEnv _tcLoc

{-------------------
 -- Unique supply --
 -------------------}

tcGetSupplyVar :: TcM (IORef Unique)
tcGetSupplyVar = getsEnv _supply

tcFreshUniq :: TcM Unique
tcFreshUniq = do
  var <- tcGetSupplyVar
  u <- readRef var
  var `writeRef` nextUnique u
  return u

{-----------
 -- Names --
 -----------}

tcFreshName :: Text -> TcM Name
tcFreshName occ = mkName occ <$> tcFreshUniq <*> tcGetLoc

tcFreshMetaTyVar :: Kind -> TcM Var
tcFreshMetaTyVar k = do
  var <-
    mkMetaTyVar
      <$> tcFreshName "t"
      <*> pure k
      <*> tcGetLevel
  tcAddUnsolved var
  return var

tcFreshMetaTy :: Kind -> TcM (Type Var)
tcFreshMetaTy k = TVar <$> tcFreshMetaTyVar k <*> pure k <*> tcGetLoc

tcFreshUnqualifiedTy :: TcM (UnqualifiedType Var)
tcFreshUnqualifiedTy = tcFreshMetaTy KindUnqualified

tcFreshDomainTy :: TcM (DomainType Var)
tcFreshDomainTy = tcFreshMetaTy KindDomain

tcFreshStageTy :: TcM (StageType Var)
tcFreshStageTy = tcFreshMetaTy KindStage

tcFreshQualifiedTy :: TcM (UnqualifiedType Var, StageType Var, DomainType Var)
tcFreshQualifiedTy = do
  dataTy <- tcFreshUnqualifiedTy
  stageTy <- tcFreshStageTy
  domTy <- tcFreshDomainTy
  return (dataTy, stageTy, domTy)

tcFreshQualifiedTy' :: TcM (QualifiedType Var)
tcFreshQualifiedTy' =
  mkQualified <$>
  tcFreshUnqualifiedTy <*>
  tcFreshStageTy <*>
  tcFreshDomainTy

tcLookupTypeOccName :: Text -> TcM (Maybe Name)
tcLookupTypeOccName occ = M.lookup occ <$> getsEnv _tcTypeRnEnv

tcLookupVarOccName :: Text -> TcM (Maybe Name)
tcLookupVarOccName occ = M.lookup occ <$> getsEnv _tcVarRnEnv

tcBindTypeOccName :: Text -> Name -> TcM a -> TcM a
tcBindTypeOccName occ name = updEnv $ over tcTypeRnEnv $ M.insert occ name

tcBindVarOccName :: Text -> Name -> TcM a -> TcM a
tcBindVarOccName occ name = updEnv $ over tcVarRnEnv $ M.insert occ name

tcLookupTyVar :: Name -> TcM (Maybe TyVar)
tcLookupTyVar name = do
  mvar <- lookupVar name
  case mvar of
    Nothing -> return Nothing
    Just var -> do
      unless (isTyVar var || isMetaTyVar var) $
        tcAddErr $ "Expecting type variable, given" <+> pretty name <> pretty '.'
      return (Just var)

tcFindTyVar :: Name -> TcM TyVar
tcFindTyVar name = do
  mvar <- tcLookupTyVar name
  case mvar of
    Just var -> return var
    Nothing -> tcThrowErr $ "Type variable" <+> pretty name <+> "not in scope."

{---------------
 -- Variables --
 ---------------}

tcSetVar :: Name -> Var -> TcM a -> TcM a
tcSetVar name var = updEnv $ over tcTyEnv (insertUM name var)

tcSetVars :: [(Name, Var)] -> TcM a -> TcM a
tcSetVars kvs = updEnv $ over tcTyEnv (unionUM (fromListUM kvs))

tcSetVarSet :: UniqMap Var -> TcM a -> TcM a
tcSetVarSet vars = updEnv $ over tcTyEnv (unionUM vars)

lookupVar :: Name -> TcM (Maybe Var)
lookupVar name = do
  genv <- getsEnv _tcTyEnv
  return $ lookupUM name genv

findVar :: Name -> TcM Var
findVar name = do
  mvar <- lookupVar name
  case mvar of
    Just var -> return var
    Nothing -> tcThrowErr $ "Variable" <+> pretty name <+> "not in scope."

findId :: Name -> TcM Id
findId name = do
  var <- findVar name
  unless (isId var) $
    tcAddErr "Expecting identifier."
  return var

{----------------------
 -- Type definitions --
 ----------------------}

tcSetType :: Name -> Kind -> TypeScheme TyVar -> TcM a -> TcM a
tcSetType name k t = updEnv $ over tcTypeDefEnv (insertUM name (k, t))

tcLookupType :: Name -> TcM (Maybe (Kind, TypeScheme TyVar))
tcLookupType name = getsEnv (lookupUM name . _tcTypeDefEnv)

tcFindType :: Name -> TcM (Kind, TypeScheme TyVar)
tcFindType name = do
  tdef <- tcLookupType name
  case tdef of
    Just var -> return var
    Nothing -> tcThrowErr $ "Type" <+> pretty name <+> "not in scope."

{-------------------------
 -- Struct declarations --
 -------------------------}

tcSetStruct :: Name -> [(Text, Type TyVar)] -> TypeScheme TyVar -> Maybe Name -> TcM ()
tcSetStruct sname fields typ mfin = do
  l <- tcGetLoc
  let
    fieldMap = M.fromList [(x, StructFieldInfo x i t) | ((x, t), i) <- zip fields [0..]]
    structEnv = StructEnv {
      _structName = sname,
      _structLocation = l,
      _structType = typ,
      _structFields = fieldMap,
      _structFinalizer = mfin
    }
  envRef <- getsEnv _tcStructEnv
  modifyRef envRef (insertUM sname structEnv)

tcLookupStruct :: Name -> TcM (Maybe StructEnv)
tcLookupStruct name = lookupUM name <$> tcGetStructsEnv

tcFindStruct :: Name -> TcM StructEnv
tcFindStruct name = do
  tstruct <- tcLookupStruct name
  case tstruct of
    Just info -> return info
    Nothing -> tcThrowErr $ "Struct" <+> pretty name <+> "not in scope."

-- TODO: should we expand synonyms?
-- i think they are already expanded but should test that further
tcIsStruct :: Type Var -> TcM Bool
tcIsStruct t = case extractHeadVar t of
  Just v -> isJust <$> tcLookupStruct (varName (unLocated v))
  _      -> return False

tcGetStructsEnv :: TcM StructsEnv
tcGetStructsEnv = readRef =<< getsEnv _tcStructEnv

{---------------
 -- Functions --
 ---------------}

-- Sets top level function parameter infromation.
tcSetTopFunParams :: Uniquable k => [(k, [ParamPassingStyle])] -> TcM a -> TcM a
tcSetTopFunParams kvs = updEnv $ over tcTopFunParams (unionUM (fromListUM kvs))

-- Returns Nothing if the name does not refer to a top-level function.
tcGetTopFunParams :: Uniquable k => k -> TcM (Maybe [ParamPassingStyle])
tcGetTopFunParams k = getsEnv (lookupUM k . _tcTopFunParams)

tcSetRnFunctions :: [(Name, [Name])] -> TcM a -> TcM a
tcSetRnFunctions kvs = updEnv $ over tcFunRnEnv (unionUM (fromListUM kvs))

tcGetRnFunction :: Name -> TcM [Name]
tcGetRnFunction name = do
  genv <- getsEnv _tcFunRnEnv
  case lookupUM name genv of
    Just se -> return se
    _       -> tcThrowErr $ "Function" <+> pretty name <+> "not in scope."

{-------------------
 -- Substitutions --
 -------------------}

normalizeSubType :: Type SubVar -> IO (Type Var)
normalizeSubType (TCon c l) = return $ TCon c l
normalizeSubType (TVar ref k l) = do
  svar <- readIORef ref
  case svar of
    SubVarRoot x -> return $ TVar x k l
    SubVarLink t -> normalizeSubType t
normalizeSubType (TApp t ts l) =
  TApp <$> normalizeSubType t <*> mapM normalizeSubType ts <*> pure l
normalizeSubType (TSelf l) = return $ TSelf l

subVar :: IORef SubVarMap -> Var -> IO SubVar
subVar envRef v = do
  subEnv <- readIORef envRef
  case lookupUM v subEnv of
    Just s -> return s
    Nothing -> do
      newSubVar <- newIORef (SubVarRoot v)
      writeIORef' envRef (insertUM v newSubVar subEnv)
      return newSubVar

typeToSubType :: IORef SubVarMap -> Type Var -> IO (Type SubVar)
typeToSubType envRef = traverse sub
  where sub = subVar envRef

getSubs :: SubVarMap -> IO (UniqMap (Type Var))
getSubs svarMap = mapMaybeUM id <$> traverse go svarMap
  where

    go :: SubVar -> IO (Maybe (Type Var))
    go varRef = do
      svar <- readIORef varRef
      case svar of
        SubVarRoot _ -> return Nothing
        SubVarLink t -> Just <$> normalizeSubType t

tcTakeSubs :: TcM (UniqMap (Type Var))
tcTakeSubs = do
  var <- getsEnv _tcSubs
  subs <- readRef var
  var `writeRef` emptyUM
  liftIO $ getSubs subs

tcAddSub :: TyVar -> Type TyVar -> TcM ()
tcAddSub k t = do
  envRef <- getsEnv _tcSubs
  t' <- liftIO $ typeToSubType envRef t
  subEnv <- readRef envRef
  case lookupUM k subEnv of
    Nothing -> do
      ref <- newRef (SubVarLink t')
      writeRef envRef (insertUM k ref subEnv)
    Just ref ->
      writeRef ref (SubVarLink t')

-- TODO: we can easily have links to links here those could be normalized for some speedup.
tcSubType :: Type Var -> TcM (Type Var)
tcSubType typ = do
  envRef <- getsEnv _tcSubs
  um <- readRef envRef
  let
    go t@TCon{} = return t
    go t@(TVar x k l) = case lookupUM x um of
      Nothing -> return t
      Just subRef -> do
        sub <- readRef subRef
        case sub of
          SubVarRoot y -> return $ TVar y k l
          SubVarLink t' -> liftIO $ normalizeSubType t'
    go (TApp t ts l) = TApp <$> go t <*> mapM go ts <*> pure l
    go (TSelf l) = pure $ TSelf l
  go typ

{---------------
 -- Unsolved  --
 ---------------}

tcAddUnsolved :: MetaTyVar -> TcM ()
tcAddUnsolved x | not (isMetaTyVar x) =
  tcSetLoc (location x) $
    tcFatal "ICE: Expecting a meta type variable!"
tcAddUnsolved x = do
  var <- getsEnv _tcUnsolved
  var `modifyRef` insertUM x x

tcTakeUnsolved :: TcM (UniqMap MetaTyVar)
tcTakeUnsolved = do
  var <- getsEnv _tcUnsolved
  unsolved <- readRef var
  var `writeRef` emptyUM
  return unsolved

tcRemoveUnsolved :: MetaTyVar -> TcM ()
tcRemoveUnsolved x = do
  var <- getsEnv _tcUnsolved
  var `modifyRef` deleteUM x

{--------------------------------
 -- Information about builtins --
 --------------------------------}

tcSetDocBuiltins :: [(T.Text, BuiltinInfo, TypeScheme TyVar)] -> TcM ()
tcSetDocBuiltins bs = do
  r <- getsEnv _tcDocBuiltins
  r `writeRef` bs


{-----------------
 -- Constraints --
 -----------------}

tcGetConstrVar :: TcM (IORef WantedConstraints)
tcGetConstrVar = getsEnv _tcConstr

tcTakeConstraints :: TcM WantedConstraints
tcTakeConstraints = do
  var <- tcGetConstrVar
  cs <- readRef var
  var `writeRef` emptyWanted
  return cs

tcAddWanted :: TypePred TyVar -> TcM ()
tcAddWanted p = do
  var <- tcGetConstrVar
  modifyRef var (addWanted p)

tcUnifyTypes :: Type Var -> Type Var -> TcM ()
tcUnifyTypes ty1 ty2 = do
  p <- PredEq ty1 ty2 <$> tcGetLoc
  tcAddWanted p

tcAddImplication :: [TypePred TyVar] -> WantedConstraints -> TcM ()
tcAddImplication ps c = do
  level <- tcGetLevel
  var <- tcGetConstrVar
  let impl = Implication level ps c
  modifyRef var (addImplication impl)

tcCollectWanted :: TcM a -> TcM (WantedConstraints, a)
tcCollectWanted act = do
  var <- newRef emptyWanted
  res <- updEnv (set tcConstr var) act
  wanted <- readRef var
  return (wanted, res)

tcAndWanted :: WantedConstraints -> TcM ()
tcAndWanted wc
  = do
      var <- tcGetConstrVar
      modifyRef var (andWanted wc)

tcAddSubConstr :: Type Var -> Type Var -> TcM ()
tcAddSubConstr l r = do
  loc <- tcGetLoc
  tcAddWanted $ PredSub l r loc

tcAddQualifyConstr :: UnqualifiedType Var -> DomainType Var -> TcM ()
tcAddQualifyConstr t d = do
  loc <- tcGetLoc
  tcAddWanted $ PredQualify t d loc

{-----------
 -- Loops --
 -----------}

tcSetInForStmt :: TcM a -> TcM a
tcSetInForStmt = updEnv $ tcInForStmt .~ True

tcLeaveForStmt :: TcM a -> TcM a
tcLeaveForStmt = updEnv $ tcInForStmt .~ False

tcIsInForStmt :: TcM Bool
tcIsInForStmt = getsEnv _tcInForStmt

{------------------------------
 -- Branching domain context --
 ------------------------------}

tcGetBranchDomain :: TcM (Maybe (DomainType TyVar))
tcGetBranchDomain = getsEnv _tcBranchDomain

tcSetBranchDomain :: DomainType TyVar -> TcM a -> TcM a
tcSetBranchDomain dom = updEnv $ tcBranchDomain ?~ dom


{-----------------
 -- Return type --
 -----------------}

tcSetReturnType :: Type Var -> TcM a -> TcM a
tcSetReturnType ty = updEnv $ tcReturnType ?~ ty

tcGetReturnType :: TcM (Type Var)
tcGetReturnType = do
  mty <- getsEnv _tcReturnType
  case mty of
    Nothing -> tcFatal "ICE: tcGetReturnType: no return type in the given context"
    Just ty -> return ty

{-----------------
 -- Type levels --
 -----------------}

tcGetLevel :: TcM Level
tcGetLevel = getsEnv _tcLevel

tcWithLevel :: Level -> TcM a -> TcM a
tcWithLevel l = updEnv $ set tcLevel l

tcWithNextLevel :: TcM a -> TcM a
tcWithNextLevel = updEnv $ tcLevel %~ (+ 1)


{------------------------------
 -- Type synonym occurrences --
 ------------------------------}

tcAddSynonymOccur :: Uniquable a => a -> Location -> TcM ()
tcAddSynonymOccur name loc = do
  ref <- getsEnv _tcSynonymOccurs
  modifyRef ref $ insertUM name loc

{------------------------------
 -- Self
 ------------------------------}

tcAllowSelf
  :: TcM a -> TcM a
tcAllowSelf
  = updEnv (tcSelf .~ True)

tcIfSelfAllowed
  :: Doc () -> TcM b -> TcM b
tcIfSelfAllowed txt act
  = do
      flag <- getsEnv _tcSelf
      if flag
        then act
        else tcThrowErr $ "Self" <+> txt <+> "outside impl blocks"

tcSetSelfType :: Type TyVar -> TcM a -> TcM a
tcSetSelfType ty = updEnv $ tcSelfType ?~ ty

tcGetSelfType :: TcM (Maybe (Type TyVar))
tcGetSelfType = getsEnv _tcSelfType
