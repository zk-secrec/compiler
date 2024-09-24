{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Core.Pretty (
    pprintCoreProgram,
    pprintCoreExpr,
)
where

import Core.Syntax
import Support.Pretty
import Parser.Syntax
import Basic.Var
import Basic.Location
import Data.Foldable
import Basic.Name
import Support.Unique

ind :: Doc a -> Doc a
ind = indent 2

ppVar :: Var -> Doc a
ppVar v = pretty (nameOccName (varName v)) <> "#" <> pretty (getUnique v)

pprintSeq' :: [Doc a] -> Doc a
pprintSeq' = hcat . punctuate comma

ppVarSeq :: [Var] -> Doc a
ppVarSeq = pprintSeq' . map ppVar

ppMaybeWith :: Maybe a -> (a -> Doc b) -> Doc b
ppMaybeWith mx f = maybe emptyDoc f mx

ppLet :: CoreLet -> Doc ann
ppLet lt = "{" <> line <> ind (ppLetBody lt) $$ "}"

ppLoc :: Location -> Doc ann
ppLoc l = "at" <+> "\'" <> pretty l <> "\'"

pprintIsVectorized :: IsVectorized -> Doc a
pprintIsVectorized IsVectorized = " vec"
pprintIsVectorized NotVectorized = ""

pprintIsSieveFn :: IsSieveFn -> Doc a
pprintIsSieveFn IsSieveFn = " sieve"
pprintIsSieveFn NotSieveFn = ""

pprintIsLambda :: IsLambda -> Doc a
pprintIsLambda IsLambda = " lambda"
pprintIsLambda NotLambda = ""

pprintCoreExpr :: CoreExpr -> Doc a
pprintCoreExpr (CeVar x) = ppVar x
pprintCoreExpr (CeLam is xs lt) = "fn" <> pprintIsSieveFn is <+> ppVarTuple xs <+> ppLet lt
pprintCoreExpr (CeLit c) = pprintConstant c
pprintCoreExpr (CeLet lt) = "{" $$ ind (ppLetBody lt) $$ "}"
pprintCoreExpr (CeCall iv f ts xs _) =
  "call" <> pprintIsVectorized iv <+> ppVar f <+>
    "[" <> pprintSeq' (map pretty ts) <> "]" <+>
    "(" <> ppVarSeq xs <> ")"
pprintCoreExpr (CeCast x t) = ppVar x <+> "as" <+> pretty t
pprintCoreExpr (CeDbgAssert x l mcl) =
  "dbg_assert" <+> ppVar x <+> ppLoc l <+> ppMaybeWith mcl ppLet
pprintCoreExpr (CeDbgAssertEq x y l mcl) =
  "dbg_assert_eq" <+> ppVar x <+> ppVar y <+> ppLoc l <+> ppMaybeWith mcl ppLet
pprintCoreExpr (CeLoop loop) = pprintLoop loop
pprintCoreExpr (CeZip pairs l) =
  "zip" <+> pprintSeq' (map (\ (x, xs) -> ppVar x <+> "in" <+> ppVar xs) pairs) <+> "with" <+> ppLet l
pprintCoreExpr (CeIfThenElse x l1 l2) =
  "if" <+> ppVar x <+> ppLet l1 $$ "else" <+>  ppLet l2
pprintCoreExpr (CeMatch x cases defcase xs) =
  "match" <+> ppVar x <+> "{" $$ vcat (fmap (ind . ppCase) cases) $$ ind ("_ ->" <+> ppVar defcase) $$ "}" <+> parens (ppVarSeq xs)
pprintCoreExpr (CeTypeIf p l1 l2) =
  "if" <+> pretty p <+> ppLet l1 $$ "else" <+> ppLet l2
pprintCoreExpr (CeStore x is y) =
  "store" <+> ppVar x <> ppOffsets is <+> "=" <+> ppVar y
pprintCoreExpr (CeStoreCtor kvs) =
  "{#" <+> pprintSeq' [ppVar k <+> "=>" <+> ppVar v | (k, v) <- kvs] <> "}"
pprintCoreExpr (CeLoad x is) = "load" <+> ppVar x <> ppOffsets is
pprintCoreExpr (CeRef x is) = "ref" <+> ppVar x <> ppOffsets is
pprintCoreExpr (CeList lst) = pprintListSyn lst
pprintCoreExpr (CeTuple xs) = "(" <> ppVarSeq xs <> ")"
pprintCoreExpr (CeStructCtor s ts xs) =
  ppVar s <+>
    "[" <> pprintSeq' (map pretty ts) <> "]" <+>
    "{" <> ppVarSeq xs <> "}"
pprintCoreExpr (CeWire shape lt) =
  "witness" <+> parens (ppVar shape) <+> ppLet lt
pprintCoreExpr (CeTypeToExpr t) = "type-to-expr" <+> pretty t
pprintCoreExpr (CeContinue k) = "continue" <+> pretty k
pprintCoreExpr (CeBreak k) = "break" <+> pretty k
pprintCoreExpr (CeTrace _l str lt) = "trace" <+> pretty (show str) <+> ppLet lt
pprintCoreExpr CeBot = "⊥"

ppCase :: (Integer, Var) -> Doc ann
ppCase (n, x) = pretty n <+> "->" <+> ppVar x

ppOffsets :: [CoreOffset] -> Doc ann
ppOffsets = cat . map go
  where
    go (COffTuple i) = "." <> pretty i
    go (COffStruct i) = "." <> pretty i
    go (COffDynamic s) = "[" <> pprintSlice s <> "]"
    go (COffKey x) = "{#" <> ppVar x <> "}"

pprintListSyn :: List Var -> Doc a
pprintListSyn (ListRange a b) = "[" <> ppVar a <+> ".." <+> ppVar b <> "]"
pprintListSyn (ListElems xs) = "[" <> ppVarSeq xs <> "]"
pprintListSyn (ListReplicate x n) = "[" <> ppVar x <+> ";" <+> ppVar n <> "]"

pprintSlice :: ArraySlice Var -> Doc a
pprintSlice (ArrayIndex x) = ppVar x
pprintSlice ArrayAll = ".."
pprintSlice (ArrayFrom a) = ppVar a <+> ".."
pprintSlice (ArrayTo b) = ".." <+> ppVar b
pprintSlice (ArrayFromTo a b) = ppVar a <+> ".." <+> ppVar b

pprintLoop :: CoreLoop -> Doc a
pprintLoop CoreForRange{..} = "for" <+> range <+> "{" $$ body $$ "}"
  where
    i = ppVar _loopVar
    begin = ppVar _loopBegin
    end = ppVar _loopEnd
    body = ind (ppLetBody _loopBody)
    range = "(" <> i <+> "in" <+> begin <+> ".." <+> end <> ")"
pprintLoop CoreForExpr{..} = "for" <+> range <+> "{" $$ body $$ "}"
  where
    i = ppVar _loopVar
    begin = ppVar _loopBegin
    end = ppVar _loopEnd
    body = ind (ppLetBody _loopBody)
    range = i <+> "in" <+> begin <+> ".." <+> end
pprintLoop CoreForever{..} = "loop" <+> "{" $$ body $$ "}"
  where
    body = ind (ppLetBody _loopBody)

ppVarTuple :: [Var] -> Doc a
ppVarTuple = ppTuple . map ppVar

ppTuple :: [Doc ann] -> Doc ann
ppTuple [d] = d
ppTuple ds = "(" <> pprintSeq' ds <> ")"

pprintPat :: CorePat -> Doc a
pprintPat (CorePat xs) = parens $ pprintSeq' $ map pprintVarWithType xs

pprintBind :: CoreBind -> Doc a
pprintBind (CoreBind recursive pat expr) = (if recursive then ("rec" <+>) else id) (pprintPat pat <+> "=" <+> pprintCoreExpr expr)

ppLetBody :: CoreLet -> Doc a
ppLetBody (CoreLet binds xs) =
  vcat (map (\b -> pprintBind b <> ";") binds) $$ ppVarTuple xs

pprintConstant :: Constant -> Doc a
pprintConstant (ConstInt n) = pretty n
pprintConstant (ConstBool b) = pretty b
pprintConstant (ConstString s) = pretty (show s) -- must escape the string
pprintConstant ConstUnit = "()"

pprintVarWithType :: Var -> Doc a
pprintVarWithType x
  | idIsMutable x = "mut" <+> varWithType
  | otherwise = varWithType
  where
    varWithType = ppVar x <+> ":" <+> pretty (idType x)

ppCoreFuncParam :: SimpleFuncParam Id -> Doc ann
ppCoreFuncParam (SimpleFuncParam ps x) = case ps of
  PassByRef -> "ref" <+> ppVar x
  PassByValue -> ppVar x

pprintCoreTopExtern :: CoreTopExtern -> Doc ann
pprintCoreTopExtern (CoreTopExtern f xs) =
  "extern fn" <> pprintVarWithType f <+> "=" <+> "\\" <> ppTuple (map ppCoreFuncParam xs) <+> "->" <+> "EXTERN"

pprintCoreTopFunction :: CoreTopFunction -> Doc ann
pprintCoreTopFunction (CoreTopFunction f xs lt is il) =
  "fn" <> pprintIsSieveFn is <> pprintIsLambda il <+> pprintVarWithType f <+> "=" <+>
      "\\" <> ppTuple (map ppCoreFuncParam xs) <+> "->" <+>
  "{" $$
    ind (ppLetBody lt) $$
  "}"

pprintCoreStructImpl :: CoreStructImpl -> Doc a
pprintCoreStructImpl (CoreStructImpl t fs) =
  "impl" <+> pretty t <+> "{" $$ ind (vcat (map pprintCoreTopFunction fs)) $$ "}"

pprintCoreProgram :: CoreProgram -> Doc a
pprintCoreProgram (CoreProgram exts funs impls) =
  vcat (map pprintCoreTopExtern exts) $$
  vcat (concatMap (map pprintCoreTopFunction . toList) funs) $$
  vcat (map pprintCoreStructImpl impls)
