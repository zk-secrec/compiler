{-# LANGUAGE RecordWildCards #-}
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

module Parser.SyntaxDump (
  dumpExpr,
  dumpStmt,
  dumpType,
  dumpTopLevel,
  dumpProgram,
  dumpLProgram,
  dumpSignature,
  dumpTypePred,
  dumpTypedProgram,
) where

import Basic.Location
import Basic.Var (idType)
import Parser.Syntax
import Support.Pretty
import Typing.Typing

import Data.Graph (flattenSCCs)

ind :: Doc a -> Doc a
ind = indent 2

withName :: String -> Doc ann -> Doc ann
withName name showIndent = pretty name <> colon $$ ind showIndent

withNameAndLoc :: String -> Location -> Doc ann -> Doc ann
withNameAndLoc name loc doc =
  pretty name <> colon <+> "//" <+> pretty loc $$ ind doc

withLocationInline :: String -> (a -> Doc ann) -> Located a -> Doc ann
withLocationInline name showInline (Located loc x) =
  pretty name <> colon <+> showInline x <+> "//" <+> pretty loc

withLocation :: String -> (a -> Doc ann) -> Located a -> Doc ann
withLocation name showIndent (Located loc x) =
  pretty name <> colon <+> "//" <+> pretty loc $$ ind (showIndent x)

maybePrint :: (a -> Doc ann) -> Maybe a -> Doc ann
maybePrint = maybe emptyDoc

dumpList :: (a -> Doc ann) -> [a] -> Doc ann
dumpList f = vcat . map f

dumpConstant :: Constant -> Doc ann
dumpConstant (ConstInt n) = pretty n
dumpConstant (ConstBool b) = pretty b
dumpConstant (ConstString s) = pretty (show s)
dumpConstant ConstUnit = "ConstUnit"

dumpCon :: TypeCon -> Doc ann
dumpCon (ConTuple n) = "ConTuple(" <> pretty n <> ")"
dumpCon (ConNat m) = "ConNat" <> parens (pretty m)
dumpCon c = pretty (show c)

dumpTypeArg :: Pretty a => TypeArgument a -> Doc ann
dumpTypeArg (TypeArg ty) = dumpType ty
dumpTypeArg (TypeArgNamedType var ty) =
  prefix <> pretty var <+> "=" <+> dumpType ty
  where
    prefix | isDomain =  "@"
           | otherwise = emptyDoc
    isDomain = case ty of
      TVar _ KindDomain _ -> True
      TCon c _ -> c `elem` domainConstructors
      _ -> False
dumpTypeArg (TypeArgQualifiedNamedType tyVar domVar ty) =
  pretty tyVar <+> "@" <> pretty domVar <+> "=" <+> dumpType ty

dumpType :: Pretty a => Type a -> Doc ann
dumpType (TCon con l)  = withNameAndLoc "TCon" l (dumpCon con)
dumpType (TVar x k _)  = "TVar:" <+> pretty x <+> parens (pretty k)
dumpType (TApp t ts l) = withNameAndLoc "TApp" l (dumpType t $$ dumpList dumpType ts)
dumpType (TSelf _)     = "TSelf"

dumpArraySlice :: Pretty a => ArraySlice (Expr a) -> Doc ann
dumpArraySlice (ArrayIndex s) = withName "ArrayIndex" (dumpExpr s)
dumpArraySlice ArrayAll = "ArrayAll"
dumpArraySlice (ArrayFrom f) = withName "ArrayFrom" (dumpExpr f)
dumpArraySlice (ArrayTo t) = withName "ArrayTo" (dumpExpr t)
dumpArraySlice (ArrayFromTo f t) = withName "ArrayFromTo" (dumpExpr f $$ dumpExpr t)

dumpLArraySlice :: Pretty a => LArraySlice (Expr a) -> Doc ann
dumpLArraySlice = withLocation "ArraySlice" dumpArraySlice

dumpListExpr :: Pretty a => List (Expr a) -> Doc ann
dumpListExpr (ListRange start end) =
  withName "ListRange" (dumpExpr start $$ dumpExpr end)
dumpListExpr (ListElems els) =
  withName "ListElems" (dumpList dumpExpr els)
dumpListExpr (ListReplicate el len) =
  withName "ListReplicate" (dumpExpr el $$ dumpExpr len)

dumpExpr :: Pretty a => Expr a -> Doc ann
dumpExpr (Ascription e t) = withName "Ascription" (dumpExpr e $$ dumpType t)
dumpExpr (Assign iv tgt src) = withName ("Assign " ++ show iv) (dumpExpr tgt $$ dumpExpr src)
dumpExpr (Block stmts mVal) = case mVal of
  Nothing -> withName "BlockStmt" (dumpList dumpStmt stmts)
  Just expr -> withName "BlockExpr" (dumpList dumpStmt stmts $$ withName "LastExpr" (dumpExpr expr))
dumpExpr (CallOper iv oper params) =
  withLocationInline ("CallOper " ++ show iv) pretty oper $$
  ind (dumpList dumpExpr params)
dumpExpr (Call iv fun tyArgs params) =
  withName ("Call " ++ show iv) $
  dumpFuncOrMethod fun $$
  ind (if null tyArgs then dumpList dumpExpr params else dumpList dumpTypeArg tyArgs $$ dumpList dumpExpr params)
dumpExpr (Cast e t) = withName "Cast" (dumpExpr e $$ dumpType t)
dumpExpr (DbgAssert e1 me2) =
  withName "DbgAssert" (dumpExpr e1 $$ maybePrint dumpExpr me2)
dumpExpr (DbgAssertEq e1 e2 me3) =
  withName "DbgAssertEq" (dumpExpr e1 $$ dumpExpr e2 $$ maybePrint dumpExpr me3)
dumpExpr (For x s e b) =
  withName "For"
  (withLocationInline "Var" pretty x $$
   dumpExpr s $$
   dumpExpr e $$
   dumpExpr b)
dumpExpr Hole = "Hole"
dumpExpr (IfThenElse c t f) =
  withName "IfThenElse" (dumpExpr c $$ dumpExpr t $$ maybePrint dumpExpr f)
dumpExpr (IndexStore e i) = withName "IndexStore" (dumpExpr e $$ dumpExpr i)
dumpExpr (Index e slice) = withName "Index" (dumpExpr e $$ dumpLArraySlice slice)
dumpExpr (Lam isf xs mt e) = withName "Lam" (dumpIsSieveFn isf $$ dumpList dumpLamParam xs $$ maybePrint dumpType mt $$ dumpExpr e)
dumpExpr (List l) = "List:" <+> dumpListExpr l
dumpExpr (Lit c) = "Lit:" <+> dumpConstant c
dumpExpr (Match e cases) = 
  withName "Match" (dumpExpr e $$ dumpList dumpCase cases)
dumpExpr (RefArg e) = withName "RefArg" (dumpExpr e)
dumpExpr (StoreCtor kvs) = withName "StoreCtor" (dumpList dumpKeyValue kvs)
dumpExpr (StructCtor x ts fs) =
  withLocationInline "StructCtor" pretty x $$
  ind (dumpList dumpTypeArg ts $$ dumpList dumpFieldCtor fs)
dumpExpr (Select e c) = withName "Select" ((
  case c of
    SelectField n -> pretty n
    SelectIndex i -> pretty i) <+> "from" $$ dumpExpr e)
dumpExpr Self = "Self"
dumpExpr (Tuple xs) = withName "Tuple" (dumpList dumpExpr xs)
dumpExpr (TypeAnnot t e) = ("//" <+> pretty t) $$ dumpExpr e
dumpExpr (Var name) = withLocationInline "Var" pretty name
dumpExpr (While cond body) = withName "While" (dumpExpr cond $$ dumpExpr body)
dumpExpr (WireExpr shape block) =
  withName "WireExpr" $
  dumpExpr shape $$
  dumpExpr block
dumpExpr (Zip pairs block) =
  withName "Zip" $
  foldr ($$) (dumpExpr block) $ 
  fmap (\ (x , xs) -> withLocationInline "Var" pretty x $$ dumpExpr xs) pairs
dumpExpr (ExprLoc _ e) = dumpExpr e
dumpExpr (Trace (Located _ msg) e) = withName "Trace" (withName "Message" (pretty msg) $$ dumpExpr e)
dumpExpr (TypePredExpr p) = withName "TypePredExpr" $ dumpTypePred p
dumpExpr (TypeIf p e1 e2) = withName "TypeIf" (dumpTypePred p $$ dumpExpr e1 $$ dumpExpr e2)
dumpExpr (TypeToExpr t) = withName "TypeToExpr" $ dumpType t

dumpKeyValue :: Pretty a => (Expr a, Expr a) -> Doc ann
dumpKeyValue (k, v) = withName "KeyValuePair" (dumpExpr k $$ dumpExpr v)

dumpFieldCtor :: Pretty a => StructFieldCtor a -> Doc ann
dumpFieldCtor (StructFieldCtor x e) =
  withName "StructFieldCtor" $
    ind (withLocationInline "Name" pretty x $$ dumpExpr e)

dumpFieldDecl :: Pretty a => StructFieldDecl a -> Doc ann
dumpFieldDecl (StructFieldDecl x t) =
  withName "StructFieldDecl" $
    ind (withLocationInline "Name" pretty x $$ dumpType t)

dumpCase :: Pretty a => (Located (Pat a), Expr a) -> Doc ann
dumpCase (p, e) =
  withLocationInline "LHS" dumpPat p $$
  ind (withName "RHS" (dumpExpr e))

dumpPat :: Pretty a => Pat a -> Doc ann
dumpPat (LitPat n) = "LitPat:" <+> pretty n
dumpPat (VarPat x) = "VarPat:" <+> pretty x
dumpPat WildCard   = "WildCard"

dumpStmt :: Pretty a => Stmt a -> Doc ann
dumpStmt (Break _) = "Break"
dumpStmt (Continue _) = "Continue"
dumpStmt (Expr e) = withName "Expr" (dumpExpr e)
dumpStmt (Let b (Binding mut x mTy) mExpr) = withName name (
  (if b then "Recursive" else emptyDoc) $$
  withLocationInline "Var" pretty x $$
  maybePrint dumpType mTy $$
  dumpExpr mExpr)
  where
    name = case mut of
      Mutable -> "Let Mutable"
      Immutable -> "Let"
dumpStmt (Return e) = withName "Return" (dumpExpr e)

dumpFuncOrMethod :: Pretty a => FuncOrMethod a -> Doc ann
dumpFuncOrMethod (Func f)
  = withLocationInline "Func" pretty f
dumpFuncOrMethod (Method self (Located loc f))
  = withName "Method" $
    dumpExpr self $$
    pretty f <+> "//" <+> pretty loc

dumpLamParam :: Pretty a => LamParam a -> Doc ann
dumpLamParam (LamParam name mt) =
  withName "LamParam" (
    withLocationInline "Var" pretty name $$
    maybePrint dumpType mt
  )

dumpFuncParam :: Pretty a => FuncParam a -> Doc ann
dumpFuncParam (FuncParam ps name ty) =
  withName "FuncParam" (
    dumpPassingStyle ps $$
    withLocationInline "Var" pretty name $$
    dumpType ty)
dumpFuncParam (SelfParam ps loc) =
  withLocationInline "SelfParam" dumpPassingStyle (Located loc ps)

dumpSimpleFuncParam :: Pretty a => SimpleFuncParam a -> Doc ann
dumpSimpleFuncParam (SimpleFuncParam ps x) = case ps of
  PassByRef -> "ref" <+> pretty x
  PassByValue -> pretty x

dumpPassingStyle :: ParamPassingStyle -> Doc ann
dumpPassingStyle PassByRef = "PassByRef"
dumpPassingStyle PassByValue = "PassByValue"

dumpSignature :: Pretty a => Signature a -> Doc ann
dumpSignature Signature{..} =
  dumpLName _sigName $$
  "IsPublic:" <+> pretty (show _sigIsPublic) $$
  withLocation "TypeParams" (dumpList dumpTypeParam) _sigTypeParameters $$
  withLocation "Params" (dumpList dumpFuncParam) _sigParameters $$
  withLocation "Constraints" (dumpList dumpTypePred) _sigConstraints $$
  withName "ReturnType" (dumpType _sigReturnType) $$
  case _sigEffect of
    Nothing -> ""
    Just twe -> withLocation "Effect" pretty twe

dumpLSignature :: Pretty a => LSignature a -> Doc ann
dumpLSignature = withLocation "Signature" dumpSignature

dumpFunction :: Pretty a => Function a -> Doc ann
dumpFunction Function{..} = dumpLSignature _funSignature $$ dumpExpr _funBody $$ dumpIsSieveFn _funIsSieve

dumpIsSieveFn :: IsSieveFn -> Doc ann
dumpIsSieveFn IsSieveFn  = "IsSieveFn"
dumpIsSieveFn NotSieveFn = "NotSieveFn"

dumpTypePred :: Pretty a => TypePred a -> Doc ann
dumpTypePred (TypePred con ts l) =
  withNameAndLoc "TypePred" l $
    withName "Con" (pretty (show con)) $$
    withName "Args" (dumpList dumpType ts)

dumpTypeParam :: Pretty a => TypeParam a -> Doc ann
dumpTypeParam (TypeParam var kind) =
  "Param:" <+> pretty var <+> parens (pretty kind)
dumpTypeParam (TypeParamQualify var mStage dom) =
  "ParamQualify:"
    <+> pretty var
    <+> maybe emptyDoc (\stage -> "$" <> pretty stage) mStage
    <+> "@" <> pretty dom

dumpTypeDef :: Pretty a => TypeDef a -> Doc ann
dumpTypeDef TypeDef{..} =
  dumpLName _tyDefName $$
  "IsPublic:" <+> pretty (show _tyDefIsPublic) $$
  withLocation "TypeParams" (dumpList dumpTypeParam) _tyDefParams $$
  withLocation "ResultKind" dumpKind _tyDefResultKind $$
  withLocation "Constraints" (dumpList dumpTypePred) _tyDefConstraints $$
  dumpType _tyDefType

dumpKind :: Kind -> Doc ann
dumpKind KindStage = "KindStage"
dumpKind KindUnqualified  = "KindUnqualified"
dumpKind KindDomain = "KindDomain"
dumpKind KindBool = "KindBool"
dumpKind KindStar = "KindStar"
dumpKind KindNat = "KindNat"
dumpKind KindRing = "KindRing"
dumpKind (KindFun k1 k2) = withName "KindFun" (dumpKind k1 $$ dumpKind k2)
dumpKind KindUnknown = "KindUnknown"
dumpKind KindEffect = "KindEffect"

dumpImport :: Import -> Doc ann
dumpImport Import{..} =
  "Items: *" $$
  "From:" <+> pretty _importName

dumpTopLevel :: Pretty a => TopLevel a -> Doc ann
dumpTopLevel (TopFunction lfun) = withLocation "Function" dumpFunction lfun
dumpTopLevel (TopExtern lsig) = withLocation "Extern" dumpSignature lsig
dumpTopLevel (TopTypeDef ldef) = withLocation "TypeDef" dumpTypeDef ldef
dumpTopLevel (TopImport limport) = withLocation "Import" dumpImport limport
dumpTopLevel (TopStructDecl lstruct) = withLocation "Struct" dumpStruct lstruct
dumpTopLevel (TopStructImpl limpl) = withLocation "Impl" dumpStructImpl limpl
dumpTopLevel (TopDefault ldef) = withLocation "Default" dumpDefault ldef

dumpStruct :: Pretty a => StructDecl a -> Doc ann
dumpStruct StructDecl{..} =
  withName "StructDecl" $
    withName "Name" (pretty _structDeclName) $$
    withName "IsPublic" (pretty _structDeclIsPublic) $$
    withName "TypeParams" (dumpList dumpTypeParam _structDeclTypeParams) $$
    withName "Fields" (dumpList dumpFieldDecl _structDeclFields)

dumpDefault :: Pretty a => Default a -> Doc ann
dumpDefault Default{..} =
  withName "Default" $
    withName "DefaultFields" $
      dumpList dumpType _defaultFields

dumpTypedDefault :: TypedDefault -> Doc ann
dumpTypedDefault TypedDefault{..} =
  withName "TypedDefault" $
    withName "DefaultFields" $
      dumpList pretty _tDefaultFields

dumpStructImpl :: Pretty a => StructImpl a -> Doc ann
dumpStructImpl StructImpl{..} =
  withName "StructImpl" $
    withName "TypeParams" (withLocation "TypeParams" (dumpList dumpTypeParam) _structImplTypeParams) $$
    withName "Type" (dumpType _structImplType) $$
    withName "Body" (dumpList dumpLFunction _structImplBody)

dumpTypedStructImpl :: TypedStructImpl -> Doc ann
dumpTypedStructImpl TypedStructImpl{..} =
  withName "TypedStructImpl" $
    withName "Type" (dumpType _tImplType) $$
    withName "Methods" (dumpList dumpTypedTopFunction _tImplMethods)

dumpProgram :: Pretty a => Program a -> Doc ann
dumpProgram Program{..} =
  dumpList dumpLImport _programImports $$
  dumpList dumpLTypeDef _programTypeDefs $$
  dumpList dumpLStruct _programStructDecls $$
  dumpLDefault _programDefaults $$
  dumpList dumpLSignature _programTopExterns $$
  dumpList dumpLFunction _programTopFunctions $$
  dumpList dumpLStructImpl _programStructImpls

dumpTypedProgram :: TypedProgram -> Doc ann
dumpTypedProgram TypedProgram{..} =
  dumpList dumpTypedTopExtern _tProgExterns $$
  dumpList dumpTypedTopFunction (flattenSCCs _tProgFunctions) $$
  dumpList dumpTypedStructImpl _tProgStructImpls $$
  dumpTypedDefault _tProgDefaults

dumpTypedTopExtern :: TypedTopExtern -> Doc ann
dumpTypedTopExtern TypedTopExtern{..} =
  withName "TypedTopExtern" $
    ("//" <+> pretty (idType _tExtName)) $$
    withName "FunName" (pretty _tExtName) $$
    withName "FunArgs" (dumpList dumpSimpleFuncParam _tExtArgs) $$
    maybe "" (withLocation "FunEffect" pretty) _tExtEff

dumpTypedTopFunction :: TypedTopFunction -> Doc ann
dumpTypedTopFunction TypedTopFunction{..} =
  withName "TypedTopFunction" $
    ("//" <+> pretty (idType _tFunName)) $$
    withName "FunName" (pretty _tFunName) $$
    withName "FunArgs" (dumpList dumpSimpleFuncParam _tFunArgs) $$
    withName "FunBody" (dumpExpr _tFunBody) $$
    maybe "" (withLocation "FunEffect" pretty) _tFunEff $$
    dumpIsSieveFn _tFunIsSieve     

dumpLName :: Pretty a => Located a -> Doc ann
dumpLName = withLocationInline "Name" pretty

dumpLProgram :: Pretty a => LProgram a -> Doc ann
dumpLProgram = withLocation "Program" dumpProgram

dumpLFunction :: Pretty a => LFunction a -> Doc ann
dumpLFunction = withLocation "Function" dumpFunction

dumpLTypeDef :: Pretty a => LTypeDef a -> Doc ann
dumpLTypeDef = withLocation "TypeDef" dumpTypeDef

dumpLStruct :: Pretty a => LStructDecl a -> Doc ann
dumpLStruct = withLocation "StructDecl" dumpStruct

dumpLStructImpl :: Pretty a => LStructImpl a -> Doc ann
dumpLStructImpl = withLocation "StructImpl" dumpStructImpl

dumpLImport :: LImport -> Doc ann
dumpLImport = withLocation "Import" dumpImport

dumpLDefault :: Pretty a => LDefault a -> Doc ann
dumpLDefault = withLocation "Default" dumpDefault

