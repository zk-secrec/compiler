{-# LANGUAGE OverloadedStrings #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Typing.Builtin
  ( initBuiltins
  , builtinTypes
  ) where

import Typing.TcM
import Basic.Name
import Basic.Var
import Data.Text (Text)
import Basic.Location
import Parser.Syntax
import Support.UniqMap

import Control.Lens
import Control.Monad
import Data.Maybe (maybeToList)
import qualified Data.Map as M
import qualified Data.Text as T


freshVar :: Kind -> String -> TcM TyVar
freshVar k occ = do
  name <- tcFreshName (T.pack occ)
  return $ mkTyVar name k

freshUnqualifiedType :: String -> TcM (TyVar, UnqualifiedType Var)
freshUnqualifiedType occ = do
  let k = KindUnqualified
  t <- freshVar k occ
  return (t, TVar t k NoLocation)

freshStageType :: String -> TcM (TyVar, StageType Var)
freshStageType occ = do
  let k = KindStage
  stage <- freshVar k occ
  return (stage, TVar stage k NoLocation)

freshDomainType :: String -> TcM (TyVar, DomainType Var)
freshDomainType occ = do
  let k = KindDomain
  dom <- freshVar k occ
  return (dom, TVar dom k NoLocation)

freshNatType :: String -> TcM (TyVar, NatType Var)
freshNatType occ = do
  let k = KindNat
  nat <- freshVar k occ
  return (nat, TVar nat k NoLocation)

freshRingType :: String -> TcM (TyVar, RingType Var)
freshRingType occ = do
  let k = KindRing
  ring <- freshVar k occ
  return (ring, TVar ring k NoLocation)

freshMixedType :: String -> TcM (TyVar , RingType Var)
freshMixedType occ = do
  (var, natTy) <- freshNatType occ
  return (var, mkPlain natTy)

mkBinHelper :: TcM (Var, RingType Var) -> (RingType Var -> UnqualifiedType Var) -> (RingType Var -> UnqualifiedType Var) -> TVStage -> TcM (TypeScheme Var)
-- NoStage means stage polymorphism
mkBinHelper freshType mkArgTy mkResTy s = do
  l <- tcGetLoc
  (var, rType) <- freshType
  let argTy = mkArgTy rType
  let resTy = mkResTy rType
  (domVar, dom) <- freshDomainType "D"
  (stageVars, stage) <- case s of
    TVPre  -> return (Nothing, mkPre)
    TVPost -> return (Nothing, mkPost)
    _      -> (_1 %~ Just) <$> freshStageType "S"
  preds <- return $ case s of
    TVPost -> [PredPostRing rType l, PredExtendedArithmetic l]
    _      -> []
  let argQTy = mkQualifiedL argTy stage dom l
  let resQTy = mkQualifiedL resTy stage dom l
  return $ mkScheme ([var] ++ maybeToList stageVars ++ [domVar]) preds $ mkFunArgs [argQTy, argQTy] resQTy

-- uint -> uint -> uint
mkBuiltinModInvert :: TcM (TypeScheme Var)
mkBuiltinModInvert = do
  (domVar, dom) <- freshDomainType "D"
  let uintTy = mkQualified (mkUnqualInt (mkPlain mkInfinite)) mkPre dom
  let ty = mkFunArgs [uintTy, uintTy] uintTy
  return $ mkScheme [domVar] [] ty

mkDivMod :: TcM (TypeScheme Var)
mkDivMod = do
  l <- tcGetLoc
  (nVar, rType) <- freshMixedType "N"
  let argTy = mkUnqualInt rType
  let resTy = mkUnqualInt rType
  (domVar, dom) <- freshDomainType "D"
  let preds = [PredPostRing rType l, PredExtendedArithmetic l]
  let argQTy = mkQualifiedL argTy mkPost dom l
  let resQTy = mkQualifiedL resTy mkPost dom l
  return $ mkScheme [nVar, domVar] preds $ mkFunArgs [argQTy, argQTy] (mkTypeTuple [resQTy, resQTy])

mkBinArithAny :: TcM (TypeScheme Var)
mkBinArithAny = mkBinHelper (freshRingType "R") mkUnqualInt mkUnqualInt TVNoStage

mkBinArithPre :: TcM (TypeScheme Var)
mkBinArithPre = mkBinHelper (freshMixedType "N") mkUnqualInt mkUnqualInt TVPre

mkBinArithPost :: TcM (TypeScheme Var)
mkBinArithPost = mkBinHelper (freshMixedType "N") mkUnqualInt mkUnqualInt TVPost

mkBinRelPre :: TcM (TypeScheme Var)
mkBinRelPre = mkBinHelper (freshRingType "R") mkUnqualInt mkUnqualBin TVPre

mkBinRelPost :: TcM (TypeScheme Var)
mkBinRelPost = mkBinHelper (freshMixedType "N") mkUnqualInt mkUnqualBin TVPost

mkModDiv :: TcM (TypeScheme Var)
mkModDiv = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let ty = mkQualified (mkUnqualInt (mkPlain n)) mkPre dom
  return $ mkScheme [nVar, domVar] [predField n l] $ mkFunArgs [ty, ty] ty

mkBinBool :: TcM (TypeScheme Var)
mkBinBool = mkBinHelper (freshRingType "R") mkUnqualBin mkUnqualBin TVNoStage

mkAssertEqUintsBools :: TcM (TypeScheme Var)
mkAssertEqUintsBools = do
  l <- tcGetLoc
  (n1Var, n1) <- freshNatType "N1"
  (domVar, dom) <- freshDomainType "D"
  let n2 = mkCon (ConNat (Finite 2))
  let u = mkTypeUIntMod n1 mkPost dom
  let b = mkTypeBoolMod n2 mkPost dom
  let list1 = mkTypeList u mkPublicDomain
  let list2 = mkTypeList b mkPublicDomain
  let scheme = mkScheme [n1Var, domVar] [predField n1 l, predField n2 l] $ mkFunArgs [list1, list2] mkTypeUnit
  return scheme

mkAssertEq :: TcM (TypeScheme Var)
mkAssertEq = do
  l <- tcGetLoc
  (t1Var, t1) <- freshUnqualifiedType "T1"
  (t2Var, t2) <- freshUnqualifiedType "T2"
  (domVar, dom) <- freshDomainType "D"
  let param1Type = mkQualified t1 mkPost dom
  let param2Type = mkQualified t2 mkPost dom
  let scheme = mkScheme [domVar, t1Var, t2Var] [PredAssertEq t1 t2 l] $ mkFunArgs [param1Type, param2Type] mkTypeUnit
  return scheme

mkAssert :: TcM (TypeScheme Var)
mkAssert = do
  l <- tcGetLoc
  (domVar, dom) <- freshDomainType "D"
  (rVar, rTy) <- freshRingType "R"
  let t = mkUnqualBin rTy
  let boolTy = mkQualifiedL t mkPost dom l
  let scheme = mkScheme [domVar, rVar] [PredPostRing rTy l] $ mkFunArgs [boolTy] mkTypeUnit
  return scheme

mkAssertZero :: TcM (TypeScheme Var)
mkAssertZero = do
  l <- tcGetLoc
  (domVar, dom) <- freshDomainType "D"
  (rVar, rTy) <- freshRingType "R"
  let t = mkUnqualInt rTy
  let uintTy = mkQualifiedL t mkPost dom l
  let scheme = mkScheme [domVar, rVar] [PredPostRing rTy l] $ mkFunArgs [uintTy] mkTypeUnit
  return scheme

mkCircuitCall :: TcM (TypeScheme Var)
mkCircuitCall = do
  l <- tcGetLoc
  (domVar, dom) <- freshDomainType "D"
  (stageVar, stage) <- freshStageType "S"
  (nVar, nTy) <- freshNatType "N"
  let t = mkUnqualBin (mkPlain nTy)
  let ty = mkQualifiedL t stage dom l
  let listlist = mkTypeList (mkTypeList ty mkPublicDomain) mkPublicDomain
  let callType = mkFunArgs [mkTypeString, listlist] listlist
  let scheme = mkScheme [nVar, stageVar, domVar] [] callType
  return scheme

mkCircuitCallU :: TcM (TypeScheme Var)
mkCircuitCallU = do
  (domVar, dom) <- freshDomainType "D"
  (stageVar, stage) <- freshStageType "S"
  let nat = mkCon (ConNat (2^64))
  let ty = mkTypeUIntMod nat stage dom
  let listt = mkTypeList ty mkPublicDomain
  return $ mkScheme [stageVar, domVar] [] $ mkFunArgs [mkTypeString, listt] listt

mkBitextractPreUint :: TcM (TypeScheme Var)
mkBitextractPreUint = do
  l <- tcGetLoc
  (nVar, nTy) <- freshNatType "N"
  let u = mkUnqualInt (mkPlain nTy)
  (domVar, dom) <- freshDomainType "D"
  let ty = mkQualifiedL u mkPre dom l
  let listt = mkTypeList ty mkPublicDomain
  return $ mkScheme [nVar, domVar] [] $ mkFunArgs [ty, mkTypeUInt mkPre mkPublicDomain] listt

mkBitextractVecHelper :: TcM (TypeScheme Var)
mkBitextractVecHelper = do
  l <- tcGetLoc
  (nVar, nTy) <- freshNatType "N"
  let u = mkUnqualInt (mkPlain nTy)
  (domVar, dom) <- freshDomainType "D"
  let ty = mkQualifiedL u mkPost dom l
  let listt = mkTypeList ty mkPublicDomain
  let arrt = mkTypeArr ty mkPublicDomain
  let listarrt = mkTypeList arrt mkPublicDomain
  return $ mkScheme [nVar, domVar] [PredVectorization l] $ mkFunArgs [listt, mkTypeU64 mkPre mkPublicDomain] listarrt

mkGetArg :: GetInputFn -> TcM (TypeScheme Var)
mkGetArg fun = do
  l <- tcGetLoc
  (tyVar, ty) <- freshUnqualifiedType "T"
  (stageVar, stage) <- freshStageType "S"
  (domVar, dom) <- freshDomainType "D"
  let tyRes = mkQualified ty stage dom
  let p = PredPossibleInput fun ty stage dom l
  return $ mkScheme [tyVar, stageVar, domVar] [p]
    (mkFunArgs [mkTypeString] tyRes)

mkBoolNot :: TcM (TypeScheme Var)
mkBoolNot = do
  l <- tcGetLoc
  (rVar, rTy) <- freshRingType "R"
  let b = mkUnqualBin rTy
  (sVar, stage) <- freshStageType "S"
  (dVar, dom) <- freshDomainType "D"
  let boolTy = mkQualifiedL b stage dom l
  return $ mkScheme [rVar, sVar, dVar] [] $ mkFunArgs [boolTy] boolTy

-- Array T => T $pre @D -> uint $pre @D
mkLength :: TcM (TypeScheme Var)
mkLength = do
  l <- tcGetLoc
  let k = KindFun KindStar KindUnqualified
  tcVar <- freshVar k "TC"
  let tc = TVar tcVar k NoLocation
  (v1, typ) <- freshUnqualifiedType "T"
  (v2, stage) <- freshStageType "S"
  (v3, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v4, lenDom) <- freshDomainType "DL"
  let argTy = mkQualified (TApp tc [elemTy] l) mkPre lenDom
  let resTy = mkTypeU64 mkPre lenDom
  let pred = PredArray tc l
  return $ mkScheme [tcVar, v1, v2, v3, v4] [pred] (mkFunArgs [argTy] resTy)

-- Array T => T $pre @D -> T $pre @D
mkUnslice :: TcM (TypeScheme Var)
mkUnslice = do
  l <- tcGetLoc
  let k = KindFun KindStar KindUnqualified
  tcVar <- freshVar k "TC"
  let tc = TVar tcVar k NoLocation
  (v1, typ) <- freshUnqualifiedType "T"
  (v2, stage) <- freshStageType "S"
  (v3, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v4, lenDom) <- freshDomainType "DL"
  let argTy = mkQualified (TApp tc [elemTy] l) mkPre lenDom
  let resTy = argTy
  let pred = PredArray tc l
  return $ mkScheme [tcVar, v1, v2, v3, v4] [pred] (mkFunArgs [argTy] resTy)

mkFreeze :: TcM (TypeScheme Var)
mkFreeze = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeList elemTy lenDom
  let resTy = mkTypeArr elemTy lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l, PredVectorization l] (mkFunArgs [argTy] resTy)

mkThaw :: TcM (TypeScheme Var)
mkThaw = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeArr elemTy lenDom
  let resTy = mkTypeList elemTy lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l, PredVectorization l] (mkFunArgs [argTy] resTy)

mkFlatten :: TcM (TypeScheme Var)
mkFlatten = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeArr elemTy lenDom
  let resTy = mkTypeArr elemTy lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l] (mkFunArgs [argTy] resTy)

mkUnflatten :: TcM (TypeScheme Var)
mkUnflatten = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeArr elemTy lenDom
  let dimTy = mkTypeList (mkTypeU64 mkPre lenDom) lenDom
  let resTy = mkTypeArr elemTy lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l] (mkFunArgs [argTy, dimTy] resTy)

mkIndexTensor :: TcM (TypeScheme Var)
mkIndexTensor = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeArr elemTy lenDom
  let dimTy = mkTypeList (mkTypeU64 mkPre lenDom) lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l] (mkFunArgs [argTy, dimTy] elemTy)

mkIndexTensor1 :: TcM (TypeScheme Var)
mkIndexTensor1 = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeArr elemTy lenDom
  let indexTy = mkTypeU64 mkPre lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l] (mkFunArgs [argTy, indexTy] argTy)

mkSize :: TcM (TypeScheme Var)
mkSize = do
  l <- tcGetLoc
  (tVar, typ) <- freshUnqualifiedType "T"
  (v1, stage) <- freshStageType "S"
  (v2, dom) <- freshDomainType "D"
  let elemTy = mkQualified typ stage dom
  (v3, lenDom) <- freshDomainType "DL"
  let argTy = mkTypeArr elemTy lenDom
  let dimTy = mkTypeList (mkTypeU64 mkPre lenDom) lenDom
  return $ mkScheme [tVar, v1, v2, v3] [PredSized typ l] (mkFunArgs [argTy] dimTy)

mkArrayToPost :: TcM (TypeScheme Var)
mkArrayToPost = do
  l <- tcGetLoc
  (v1 , typ) <- freshUnqualifiedType "T"
  (v2 , dom) <- freshDomainType "D"
  let argElemTy = mkQualified typ mkPre dom
  let resElemTy = mkQualified typ mkPost dom
  let argTy = mkTypeArr argElemTy mkPublicDomain
  let resTy = mkTypeArr resElemTy mkPublicDomain
  return $ mkScheme [v1, v2] [PredVectorization l] (mkFunArgs [argTy] resTy)

mkArrayToProver :: TcM (TypeScheme Var)
mkArrayToProver = do
  (nVar, nTy) <- freshNatType "N"
  let u = mkUnqualInt (mkPlain nTy)
  let argElemTy = mkQualified u mkPost mkVerifierDomain
  let resElemTy = mkQualified u mkPost mkProverDomain
  let argTy = mkTypeArr argElemTy mkPublicDomain
  let resTy = mkTypeArr resElemTy mkPublicDomain
  return $ mkScheme [nVar] [] (mkFunArgs [argTy] resTy)

mkMakeUnknown :: TcM (TypeScheme Var)
mkMakeUnknown = do
  (v1, typ) <- freshUnqualifiedType "T"
  (v2, stage) <- freshStageType "S"
  (v3, dom) <- freshDomainType "D"
  let argTy = mkQualified typ stage dom
  let resTy = argTy
  return $ mkScheme [v1, v2, v3] [] (mkFunArgs [argTy] resTy)

mkMakeNotUnknown :: TcM (TypeScheme Var)
mkMakeNotUnknown = do
  l <- tcGetLoc
  (rVar, rTy) <- freshRingType "R"
  let u = mkUnqualInt rTy
  (domVar, dom) <- freshDomainType "D"
  let uintPost = mkQualifiedL u mkPost dom l
  let uintPre = mkQualifiedL u mkPre dom l
  return $ mkScheme [rVar, domVar] [] (mkFunArgs [uintPost, uintPre] uintPost)

mkUintNPreMatrixProd :: TcM (TypeScheme Var)
mkUintNPreMatrixProd = do
  l <- tcGetLoc
  (rVar, rTy) <- freshRingType "R"
  let u = mkUnqualInt rTy
  (domVar, dom) <- freshDomainType "D"
  let uintPre = mkQualifiedL u mkPre dom l
  let listTy = mkTypeList uintPre mkPublicDomain
  let listListTy = mkTypeList listTy mkPublicDomain
  return $ mkScheme [rVar, domVar] [] (mkFunArgs [listListTy, listListTy] listListTy)

mkChallenge :: TcM (TypeScheme Var)
mkChallenge = do
  l <- tcGetLoc
  let argTy = mkTypeUInt mkPre mkPublicDomain
  (rVar, rTy) <- freshRingType "R"
  let u = mkUnqualInt rTy
  let chalTy = mkQualified u mkPre mkVerifierDomain
  let resTy = mkTypeList chalTy mkPublicDomain
  return $ mkScheme [rVar] [PredPostRing rTy l, PredChallenge rTy l] (mkFunArgs [argTy] resTy)

mkMakeWaksmanNetwork :: TcM (TypeScheme Var)
mkMakeWaksmanNetwork = do
  let uintType = mkTypeU64 mkPre mkPublicDomain
  let uintListType = mkTypeList uintType mkPublicDomain
  return $ mkScheme [] [] (mkFunArgs [uintType] uintListType)

mkGetSortingPermutation :: TcM (TypeScheme Var)
mkGetSortingPermutation = do
  (v, dom) <- freshDomainType "D"
  let uintListType = mkTypeList (mkTypeUInt mkPre dom) mkPublicDomain
  let u64ListType = mkTypeList (mkTypeU64 mkPre dom) mkPublicDomain
  return $ mkScheme [v] [] (mkFunArgs [uintListType] u64ListType)

mkPermutationSwitches :: TcM (TypeScheme Var)
mkPermutationSwitches = do
  (v, dom) <- freshDomainType "D"
  let argTy = mkTypeList (mkTypeU64 mkPre dom) mkPublicDomain
  let resTy = mkTypeList (mkTypeBool mkPre dom) mkPublicDomain
  return $ mkScheme [v] [] (mkFunArgs [argTy] resTy)

mkFieldBitWidth :: TcM (TypeScheme Var)
mkFieldBitWidth =
  return $ mkScheme [] [] (mkFunArgs [mkTypePubUInt] (mkTypeU64 mkPre mkPublicDomain))

-- string $pre @D -> ()
mkDbgPrint :: TcM (TypeScheme  Var)
mkDbgPrint = do
  (v, dom) <- freshDomainType "D"
  let argTy = mkQualified (mkCon ConString) mkPre dom
  return $ mkScheme [v] [] (mkFunArgs [argTy] mkTypeUnit)

-- string $pre @D -> string $pre @D -> string $pre @D
mkStringAppend :: TcM (TypeScheme  Var)
mkStringAppend = do
  (v, dom) <- freshDomainType "D"
  let strTy = mkQualified (mkCon ConString) mkPre dom
  return $ mkScheme [v] [] (mkFunArgs [strTy, strTy] strTy)

-- ToString T => T $pre @D -> string $pre @D
mkToString :: TcM (TypeScheme Var)
mkToString = do
  l <- tcGetLoc
  (tyVar, u) <- freshUnqualifiedType "T"
  (domVar, v) <- freshDomainType "D"
  let argTy = mkQualified u mkPre v
  let pred = PredToString u l
  return $ mkScheme [tyVar, domVar] [pred] (mkFunArgs [argTy] (mkQualified (mkCon ConString) mkPre v))

mkDefaultValue :: TcM (TypeScheme Var)
mkDefaultValue = do
  l <- tcGetLoc
  (v1, typ) <- freshUnqualifiedType "T"
  (v2, stage) <- freshStageType "S"
  (v3, dom) <- freshDomainType "D"
  let tyArg = mkTypeUnit
  let tyRes = mkQualifiedL typ stage dom l
  let pred = PredHasDefaultValue [] tyRes l
  return $ mkScheme [v1, v2, v3] [pred] (mkFunArgs [tyArg] tyRes)

mkBitextract :: TcM (TypeScheme Var)
mkBitextract = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  return $ mkScheme [nVar, domVar] [predField n l, PredExtendedArithmetic l] $ mkFunArgs [u] arrTy

mkAssertPerm :: TcM (TypeScheme Var)
mkAssertPerm = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  return $ mkScheme [nVar, domVar] [predField n l, PredPermutationCheck l] $ mkFunArgs [arrTy, arrTy] mkTypeUnit

mkBinArithVec :: TcM (TypeScheme Var)
mkBinArithVec = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  return $ mkScheme [nVar, domVar] [predField n l, PredVectors l] $ mkFunArgs [arrTy, arrTy] arrTy

mkBinArithVecC :: TcM (TypeScheme Var)
mkBinArithVecC = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  let pubIntTy = mkPublic (mkUnqualInt (mkPlain n))
  return $ mkScheme [nVar, domVar] [predField n l, PredVectors l] $ mkFunArgs [arrTy, pubIntTy] arrTy

mkBinArithVecScalar :: TcM (TypeScheme Var)
mkBinArithVecScalar = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  return $ mkScheme [nVar, domVar] [predField n l, PredVectors l] $ mkFunArgs [arrTy, u] arrTy

mkFoldVec :: TcM (TypeScheme Var)
mkFoldVec = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  return $ mkScheme [nVar, domVar] [predField n l, PredVectors l] $ mkFunArgs [arrTy] u

mkBinFoldVec :: TcM (TypeScheme Var)
mkBinFoldVec = do
  l <- tcGetLoc
  (nVar, n) <- freshNatType "N"
  (domVar, dom) <- freshDomainType "D"
  let u = mkQualified (mkUnqualInt (mkPlain n)) mkPost dom
  let arrTy = mkTypeArr u mkPublicDomain
  return $ mkScheme [nVar, domVar] [predField n l, PredVectors l] $ mkFunArgs [arrTy, arrTy] u

builtinTypes :: [(T.Text, BuiltinInfo, TcM (TypeScheme Var))]
builtinTypes =
   [ ("+" , BuiltinAdd, mkBinArithAny)
   , ("-" , BuiltinSub, mkBinArithAny)
   , ("*" , BuiltinMul, mkBinArithAny)
   , ("/" , BuiltinDiv, mkBinArithPre)
   , ("mod_div" , BuiltinModDiv, mkModDiv)
   , ("%" , BuiltinMod, mkBinArithPre)
   , ("^" , BuiltinXor, mkBinBool)
   , ("&" , BuiltinAnd, mkBinBool)
   , ("|" , BuiltinOr, mkBinBool)
   , ("!" , BuiltinNeg, mkBoolNot )
   , ("==", BuiltinEq, mkBinRelPre )
   , ("!=", BuiltinNeq, mkBinRelPre )
   , ("<" , BuiltinLt, mkBinRelPre )
   , ("<=", BuiltinLe, mkBinRelPre )
   , (">" , BuiltinGt, mkBinRelPre )
   , (">=", BuiltinGe, mkBinRelPre )
   , ("xor", BuiltinBoolXor, mkBinBool )
   , ("call", BuiltinCircuitCall, mkCircuitCall)
   , ("callu", BuiltinCircuitCallU, mkCircuitCallU)
   , ("assert", BuiltinAssert, mkAssert)
   , ("assert_eq", BuiltinAssertEq, mkAssertEq)
   , ("assert_eq_uints_bools", BuiltinAssertEqUintsBools, mkAssertEqUintsBools)
   , ("assert_zero", BuiltinAssertZero, mkAssertZero)
   , ("get_instance", BuiltinGetInstance, mkGetArg GetInstance)
   , ("get_public", BuiltinGetPublic, mkGetArg GetPublic)
   , ("get_witness", BuiltinGetWitness, mkGetArg GetWitness)
   , ("challenge", BuiltinChallenge, mkChallenge)
   , ("length", BuiltinLength, mkLength)
   , ("unslice", BuiltinUnslice, mkUnslice)
   , ("array_to_post", BuiltinArrayToPost, mkArrayToPost)
   , ("array_to_prover", BuiltinArrayToProver, mkArrayToProver)
   , ("freeze", BuiltinFreeze, mkFreeze)
   , ("thaw", BuiltinThaw, mkThaw)
   , ("flatten", BuiltinFlatten, mkFlatten)
   , ("unflatten", BuiltinUnflatten, mkUnflatten)
   , ("index_tensor", BuiltinIndexTensor, mkIndexTensor)
   , ("index_tensor_1", BuiltinIndexTensor1, mkIndexTensor1)
   , ("size", BuiltinSize, mkSize)
   , ("__make_waksman_network", BuiltinMakeWaksmanNetwork, mkMakeWaksmanNetwork)
   , ("__get_sorting_permutation", BuiltinGetSortingPermutation, mkGetSortingPermutation)
   , ("__permutation_switches", BuiltinPermutationSwitches, mkPermutationSwitches)
   , ("field_bit_width", BuiltinFieldBitWidth, mkFieldBitWidth)
   , ("dbg_print", BuiltinDbgPrint, mkDbgPrint)
   , ("string_append", BuiltinStringAppend, mkStringAppend)
   , ("to_string", BuiltinToString, mkToString)
   , ("__default_value", BuiltinDefaultValue, mkDefaultValue)
   , ("__mod_invert", BuiltinModInvert, mkBuiltinModInvert)
   , ("bitextract_pre_uint", BuiltinBitextractPreUint, mkBitextractPreUint)
   , ("bitextract_vec_helper", BuiltinBitextractVecHelper, mkBitextractVecHelper)
   , ("make_unknown", BuiltinMakeUnknown, mkMakeUnknown)
   , ("make_not_unknown", BuiltinMakeNotUnknown, mkMakeNotUnknown)
   , ("uint_n_pre_matrix_prod", BuiltinUintNPreMatrixProd, mkUintNPreMatrixProd)
   , ("__lt", BuiltinPluginLT, mkBinRelPost)
   , ("__le", BuiltinPluginLE, mkBinRelPost)
   , ("__div", BuiltinPluginDiv, mkBinArithPost)
   , ("__divmod", BuiltinPluginDivMod, mkDivMod)
   , ("__bitextract", BuiltinPluginBitextract, mkBitextract)
   , ("__assert_perm", BuiltinPluginAssertPerm, mkAssertPerm)
   , ("__add", BuiltinPluginAdd, mkBinArithVec)
   , ("__mul", BuiltinPluginMul, mkBinArithVec)
   , ("__addc", BuiltinPluginAddC, mkBinArithVecC)
   , ("__mulc", BuiltinPluginMulC, mkBinArithVecC)
   , ("__add_scalar", BuiltinPluginAddScalar, mkBinArithVecScalar)
   , ("__mul_scalar", BuiltinPluginMulScalar, mkBinArithVecScalar)
   , ("__sum", BuiltinPluginSum, mkFoldVec)
   , ("__prod", BuiltinPluginProd, mkFoldVec)
   , ("__dotprod", BuiltinPluginDotProd, mkBinFoldVec)
   ]

updateBuiltins :: [(Text, Name, Var)] -> Env -> Env
updateBuiltins binds = updateRns . updateTys
  where
    updateRns = tcVarRnEnv %~
      (`M.union` M.fromList [(occ, name) | (occ, name, _) <- binds])
    updateTys = tcTyEnv %~
      (`unionUM` fromListUM [(name, var) | (_, name, var) <- binds])

initBuiltins :: TcM a -> TcM a
initBuiltins cont = do
  binds <- forM builtinTypes $ \(occ, info, act) -> do
    uniq <- tcFreshUniq
    let name = mkBuiltinName occ info uniq NoLocation
    ty <- act
    return (occ, info, ty, name, mkId name Immutable ty)
  tcSetDocBuiltins [(occ, info, ty) | (occ, info, ty, _, _) <- binds]
  updEnv (updateBuiltins [(occ, name, var) | (occ, _, _, name, var) <- binds]) $
    cont
