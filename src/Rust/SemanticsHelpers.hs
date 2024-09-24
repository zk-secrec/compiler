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

-- Functions from the previous IR.SemanticsCommon that are also used by the Rust backend.
module Rust.SemanticsHelpers where

import Basic.Name
import Basic.Var
import Core.Pretty
import Core.Syntax
import Parser.SyntaxDump
import Rust.PrimitiveTypes
import Support.Pretty
import Support.Unique
import Support.UniqMap
import Typing.Type

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T

subTypeInVar :: UniqMap (Type Var) -> Var -> Var
subTypeInVar um x =
  let
    TForAll qs ps t = idType x
    t' = subType um t
    mutability = if idIsMutable x then Mutable else Immutable
  in
    mkId (varName x) mutability (TForAll qs ps t')

-- Remove statements of the form
--   let y = x
-- by replacing uses of y by x.
-- This is especially important when x is an array, as otherwise the whole array may be copied.
-- The y = x is removed only when x and y have the same mutability and the same primitiveness, as otherwise x and y are not the same.
removeCopiesFromCoreLet :: CoreLet -> CoreLet
removeCopiesFromCoreLet = removeCopiesCoreLet (Map.empty, emptyUM)

removeCopiesCoreLet :: (Map Var Var, UniqMap (Type Var)) -> CoreLet -> CoreLet
removeCopiesCoreLet copyMap =
  let
    fwd x = Map.findWithDefault x x (fst copyMap)
    fwdInOffset = fmap fwd
  in
    \case
      CoreLet [] retVars ->
        CoreLet [] (map fwd retVars)
      CoreLet (bind : binds) retVars ->
        case bind of
          CoreBind r (CorePat [y]) e | isTypePrimitive (idToType y) /= isTypePrimitive (idToType (subTypeInVar (snd copyMap) y)) ->
            let
              -- replace stage variables whose value was fixed in a stage-typeif (if pre / if post)
              y' = subTypeInVar (snd copyMap) y
              copyMap' = (Map.insert y y' (fst copyMap), snd copyMap)
              bind' = CoreBind r (CorePat [y']) e
            in
              removeCopiesCoreLet copyMap' $ CoreLet (bind' : binds) retVars
          CoreBind False (CorePat [y]) (CeVar x) | idIsMutable y == idIsMutable x && isTypePrimitive (idToType x) == isTypePrimitive (idToType y) ->
            removeCopiesCoreLet (Map.insert y (fwd x) (fst copyMap), snd copyMap) $ CoreLet binds retVars
          CoreBind recursive pat e ->
            let
              e' =
                case e of
                  CeBot -> CeBot
                  CeVar x -> CeVar $ fwd x
                  CeLit c -> CeLit c
                  CeLet cl -> CeLet $ removeCopiesCoreLet copyMap cl
                  CeCall iv f ts xs l -> CeCall iv f ts (map fwd xs) l
                  CeCast x t -> CeCast (fwd x) t
                  CeDbgAssert x l cl -> CeDbgAssert (fwd x) l (removeCopiesCoreLet copyMap <$> cl)
                  CeDbgAssertEq x y l cl -> CeDbgAssertEq (fwd x) (fwd y) l (removeCopiesCoreLet copyMap <$> cl)
                  CeLoop (CoreForExpr x x1 x2 cl) ->
                    CeLoop (CoreForExpr x (fwd x1) (fwd x2) (removeCopiesCoreLet copyMap cl))
                  CeLoop (CoreForRange x x1 x2 cl) ->
                      CeLoop (CoreForRange x (fwd x1) (fwd x2) (removeCopiesCoreLet copyMap cl))
                  CeLoop (CoreForever cl) ->
                      CeLoop (CoreForever (removeCopiesCoreLet copyMap cl))
                  CeIfThenElse x cl1 cl2 -> CeIfThenElse (fwd x) (removeCopiesCoreLet copyMap cl1) (removeCopiesCoreLet copyMap cl2)
                  CeStoreCtor assocs -> CeStoreCtor (map (\ (x,y) -> (fwd x, fwd y)) assocs)
                  CeStore x offs y -> CeStore (fwd x) (map fwdInOffset offs) (fwd y)
                  CeLoad x offs -> CeLoad (fwd x) (map fwdInOffset offs)
                  CeRef x offs -> CeRef (fwd x) (map fwdInOffset offs)
                  CeList list -> CeList $ fmap fwd list
                  CeTuple xs -> CeTuple (map fwd xs)
                  CeStructCtor s ts xs -> CeStructCtor s ts (map fwd xs)
                  CeWire shape cl -> CeWire (fwd shape) (removeCopiesCoreLet copyMap cl)
                  CeTypeIf p cl1 cl2 ->
                    let
                      (cm, stageVarMap) = copyMap
                      (svm1, svm2) =
                        case p of
                          PredPre (TVar x KindStage _) _ -> (insertUM x mkPre stageVarMap, insertUM x mkPost stageVarMap)
                          PredPost (TVar x KindStage _) _ -> (insertUM x mkPost stageVarMap, insertUM x mkPre stageVarMap)
                          _ -> (stageVarMap, stageVarMap)
                      copyMap1 = (cm, svm1)
                      copyMap2 = (cm, svm2)
                    in
                      CeTypeIf p (removeCopiesCoreLet copyMap1 cl1) (removeCopiesCoreLet copyMap2 cl2)
                  CeTypeToExpr t -> CeTypeToExpr t
                  CeContinue i -> CeContinue i
                  CeBreak i -> CeBreak i
                  CeTrace l s e -> CeTrace l s (removeCopiesCoreLet copyMap e)
                  CeZip pairs e ->
                    let
                      pairs' = flip map pairs $ \ (x, xs) -> (x, fwd xs)
                    in
                      CeZip pairs' (removeCopiesCoreLet copyMap e)
                  CeMatch x pairs cl xs ->
                    let
                      pairs' = fmap (\ (n, x) -> (n, fwd x)) pairs
                    in
                      CeMatch (fwd x) pairs' (fwd cl) (map fwd xs)
                  _ -> error ("removeCopiesCoreLet: unsupported expression: " ++ showCoreExpr e)
            in
              case removeCopiesCoreLet copyMap $ CoreLet binds retVars of
                CoreLet binds' retVars' -> CoreLet (CoreBind recursive pat e' : binds') retVars'

showCoreExpr :: CoreExpr -> String
showCoreExpr = render . pprintCoreExpr

showType :: Type Var -> String
showType = render . dumpType

typeSchemeToType :: TypeScheme a -> Type a
typeSchemeToType (TForAll _ _ t) = t -- remove the (top-level) forall, there will still be type variables in t to detect polymorphism

idToType :: Id -> Type Var
idToType = typeSchemeToType . idType

idToString :: Id -> String
idToString id
  | isBuiltin name = T.unpack txt
  | otherwise = T.unpack txt ++ '_' : show (getUnique name)
  where
    name = varName id
    txt = nameOccName name

idToBaseString :: Var -> String
idToBaseString = render . pretty . nameOccName . varName

funIdToString :: Id -> String
funIdToString fname =
  let
    baseName = idToBaseString fname
  in
    if baseName == T.unpack mainFName then baseName else idToString fname

varToString :: Var -> String
varToString x = T.unpack txt ++ '_' : show (getUnique name)
  where
    name = varName x
    txt = nameOccName name
