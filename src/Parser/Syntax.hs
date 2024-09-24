{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Parser.Syntax (
  -- Abstract syntax tree:
  ArraySlice(..),
  Binding(..),
  Constant(..),
  Default(..),
  Expr(..),
  FuncIdentifier(..),
  FuncOrMethod(..),
  FuncParam(..),
  Function(..),
  Import(..),
  IsSieveFn(..),
  IsVectorized(..),
  List(..),
  Module,
  Pat(..),
  Program(..),
  StructDecl(..),
  StructFieldCtor(..),
  StructFieldDecl(..),
  StructImpl(..),
  Selector(..),
  Signature(..),
  Stmt(..),
  TopLevel(..),
  TypeArgument(..),
  TypeDef(..),
  TypeParam(..),
  LamParam(..),
  SimpleFuncParam(..),
  ParamPassingStyle(..),
  module Typing.Type,

  -- Types with attached location:
  LArraySlice,
  LFunction,
  LImport,
  LList,
  LProgram,
  LStructDecl,
  LSignature,
  LTypeDef,
  LStructImpl,
  LDefault,

  allSigTypeVars,
  getTyParamNames,
  occurVars,
  sigIsPublic,
  signParams,
  sigTypeParamVars,
  implTypeParamVars,
  structImplBody,
  defaultFields,
  varsDefinedInStmt,
  elemsInList,
  traverseExprInProgram,
  traverseEffInTopLevel,
  traverseMatchInExpr,
  traverseTypeInExpr,
  funcParamName,
  paramNameIfAny,
  getLValueTarget,
  viewForExpr,
  isLitPat,
) where

import Basic.Location
import Basic.Fixity
import Parser.Effect (PolymorphicTypeWithEffect)
import Support.UniqMap
import Support.Unique (Uniquable)
import Typing.Type

import Control.Lens hiding (List)
import Data.Function
import Data.List (nubBy)
import Data.Maybe (maybeToList)
import qualified Data.Text as T


data Constant
  = ConstInt Integer
  | ConstBool Bool
  | ConstString String
  | ConstUnit

data TypeArgument name
  = TypeArg (Type name)
  | TypeArgNamedType (Located name) (Type name) -- Name = Type
  -- Name @Domain = Type
  | TypeArgQualifiedNamedType (Located name) (Located name) (Type name)
  deriving (Functor, Foldable, Traversable)

typeInTypeArgument :: Lens' (TypeArgument name) (Type name)
typeInTypeArgument f (TypeArg t) = TypeArg <$> f t
typeInTypeArgument f (TypeArgNamedType x t) = TypeArgNamedType x <$> f t
typeInTypeArgument f (TypeArgQualifiedNamedType x y t) = TypeArgQualifiedNamedType x y <$> f t

data IsSieveFn = IsSieveFn | NotSieveFn -- whether a given function/lambda is translated to a SIEVE IR function
  deriving (Eq, Show)

data IsVectorized = IsVectorized | NotVectorized -- whether a function call is vectorized
  deriving (Eq, Show)

data ArraySlice a
  = ArrayIndex a     -- x[i]
  | ArrayAll         -- x[..]
  | ArrayFrom a      -- x[begin ..]
  | ArrayTo a        -- x[.. end]
  | ArrayFromTo a a  -- x[begin .. end]
  deriving (Functor, Foldable, Traversable)

data List a
  = ListRange a a      -- [begin .. end] where end is excluded
  | ListElems [a]      -- [v1 , v2 , ..., vn]
  | ListReplicate a a  -- [value ; times]
  deriving (Functor, Foldable, Traversable)

elemsInList
  :: (Applicative f)
  => (a -> f a) -> List a -> f (List a)
elemsInList f (ListRange lo hi)
  = ListRange <$> f lo <*> f hi
elemsInList f (ListElems as)
  = ListElems <$> traverse f as
elemsInList f (ListReplicate a n)
  = ListReplicate <$> f a <*> pure n

-- | Either text for struct selector or index for tuple selector
data Selector
  = SelectField T.Text
  | SelectIndex Int

data StructFieldCtor name
  = StructFieldCtor
  { _structFieldCtorName :: Located T.Text
  , _structFieldCtorExpr :: Expr name
  }
  deriving (Functor, Foldable, Traversable)

exprInStructFieldCtor :: Lens' (StructFieldCtor name) (Expr name)
exprInStructFieldCtor f (StructFieldCtor x e) = StructFieldCtor x <$> f e

data FuncOrMethod name
  = Func { _fname :: Located name } -- f
  | Method                          -- s.f
    { _self :: Expr name
    , _fname :: Located name
    }
  deriving (Functor, Foldable, Traversable)

exprInFuncOrMethod :: Traversal' (FuncOrMethod name) (Expr name)
exprInFuncOrMethod _ m@(Func _)   = pure m
exprInFuncOrMethod f (Method s m) = Method <$> f s <*> pure m

data Expr name
  = Ascription (Expr name) (Type name) -- expr : type
  | Assign IsVectorized (Expr name) (Expr name) -- x[i] = e
  | Block [Stmt name] (Maybe (Expr name)) -- { let p1 = e1 ; ... ; ret_expr }
  | Call IsVectorized (FuncOrMethod name) [TypeArgument name] [Expr name] -- f::[t1, ..., tn](e1, ..., em)
  | CallOper IsVectorized (Located name) [Expr name] -- unary and binary operators
  | Cast (Expr name) (Type name) -- e as t
  | DbgAssert (Expr name) (Maybe (Expr name)) -- dbg_assert (e1, e2?)
  | DbgAssertEq (Expr name) (Expr name) (Maybe (Expr name)) -- dbg_assert_eq (e1, e2, e3?)
  | For (Located name) (Expr name) (Expr name) (Expr name) -- for i in start .. end expr
  | Hole
  | IfThenElse (Expr name) (Expr name) (Maybe (Expr name)) -- if e1 { e2 } else { e3 }
  | IndexStore (Expr name) (Expr name) -- expr{#expr}
  | Index (Expr name) (LArraySlice (Expr name)) -- expr[slice]
  | Lam IsSieveFn [LamParam name] (Maybe (Type name)) (Expr name) -- fn (p1, .., pn) expr or fn (p1, .., pn) -> t expr
  | List (List (Expr name)) -- [e1, ..., en] or [e1 ; e2] or [e1 .. e2]
  | Lit Constant -- c
  | Match (Expr name) [(Located (Pat name), Expr name)] -- match e0 {p1 => { e1 }, p2 => { e2 }, ... pn => { en } }
  | RefArg (Expr name) -- ref e, only occurs in call position
  | Select (Expr name) Selector -- x.i or x.name
  | Self -- self
  | StoreCtor [(Expr name, Expr name)]
  | StructCtor (Located name) [TypeArgument name] [StructFieldCtor name] -- struct_name { f1 : e1, ..., fn : en }
  | Trace (Located String) (Expr name) -- trace "message" e
  | Tuple [Expr name] -- (e1, ..., en)
  | TypePredExpr (TypePred name) -- pre $S or post $S or @D1 <= @D2
  | Var (Located name) -- x
  | While (Expr name) (Expr name) -- while e1 e2
  | WireExpr (Expr name) (Expr name) -- wire shape_expr res_expr
  | Zip [(Located name, Expr name)] (Expr name) -- zip x_1 in xs_1, ..., x_n in xs_n with { ... }
  -- INTERNAL. Location annotations added by the parser.
  | ExprLoc Location (Expr name)
  -- INTERNAL. Type annotations added by the type checker.
  | TypeAnnot (Type name) (Expr name)
  -- INTERNAL. Generated by type checker when regular if expression
  -- conditional can occur in type level.
  | TypeIf (TypePred name) (Expr name) (Expr name)
  -- INTERNAL. Generated by type checker when type variable of kind Nat
  -- occurs in an expression.
  | TypeToExpr (Type name)
  deriving (Functor, Foldable, Traversable)

traverseMatchInExpr :: Traversal' (Expr name) (Expr name)
traverseMatchInExpr f = \ case
  e@(Match _ _) -> f e
  e             -> plate (traverseMatchInExpr f) e

data Pat name -- Supposedly, there is no need for annotating types of patterns
  = LitPat Integer
  | VarPat name
  | WildCard
  deriving (Functor, Foldable, Traversable)

isLitPat
  :: Pat name -> Bool
isLitPat (LitPat _)
  = True
isLitPat _
  = False

instance HasLocation (Expr name) where
  type UnLocated (Expr name) = Expr name

  stripLocation (ExprLoc _ e) = stripLocation e
  stripLocation e             = e

  location (ExprLoc l _) = l
  location (TypeAnnot _ e) = location e
  location _ = NoLocation

  setLocation x l = ExprLoc l (stripLocation x)

instance Plated (Expr name) where
  plate f expr = case expr of
    Ascription e t -> Ascription <$> f e <*> pure t
    Assign iv x e -> Assign iv <$> f x <*> f e
    Block bs me -> Block <$> traverse (traverseExprInStmt f) bs <*> traverse f me
    Call iv fom vs es -> Call iv <$> exprInFuncOrMethod f fom <*> pure vs <*> traverse f es
    CallOper iv o es -> CallOper iv o <$> traverse f es
    Cast e t -> Cast <$> f e <*> pure t
    DbgAssert e1 me2 -> DbgAssert <$> f e1 <*> traverse f me2
    DbgAssertEq e1 e2 me3 -> DbgAssertEq <$> f e1 <*> f e2 <*> traverse f me3
    ExprLoc l e -> ExprLoc l <$> f e
    For x e1 e2 e3 -> For x <$> f e1 <*> f e2 <*> f e3
    Hole -> pure expr
    IfThenElse e1 e2 e3 -> IfThenElse <$> f e1 <*> f e2 <*> traverse f e3
    IndexStore e i -> IndexStore <$> f e <*> f i
    Index e s -> Index <$> f e <*> traverse (traverse f) s
    Lam isf xs mt e -> Lam isf xs mt <$> f e
    List lst -> List <$> traverse f lst
    Lit {} -> pure expr
    Match e cases -> Match <$> f e <*> traverse (_2 f) cases
    RefArg e -> RefArg <$> f e
    StoreCtor kvs -> StoreCtor <$> traverse (both f) kvs
    StructCtor x as fs -> StructCtor x as <$> traverse (exprInStructFieldCtor f) fs
    Select e c -> Select <$> f e <*> pure c
    Self -> pure expr
    Tuple es -> Tuple <$> traverse f es
    Trace str e -> Trace str <$> f e
    TypeAnnot t e -> TypeAnnot t <$> f e
    TypeIf p e1 e2 -> TypeIf p <$> f e1 <*> f e2
    TypePredExpr p -> pure $ TypePredExpr p
    TypeToExpr t -> pure $ TypeToExpr t
    Var {} -> pure expr
    While e1 e2 -> While <$> f e1 <*> f e2
    WireExpr e1 e2 -> WireExpr <$> f e1 <*> f e2
    Zip pairs e -> Zip <$> traverse (traverse f) pairs <*> f e

traverseTypeInExpr :: Traversal' (Expr name) (Type name)
traverseTypeInExpr f (Ascription e t) = Ascription <$> traverseTypeInExpr f e <*> f t
traverseTypeInExpr f (Block bs me) = Block <$> traverse (traverseTypeInStmt f) bs <*> traverse (traverseTypeInExpr f) me
traverseTypeInExpr f (Call iv fom ts es) = Call iv <$> exprInFuncOrMethod (traverseTypeInExpr f) fom <*> traverse (typeInTypeArgument f) ts <*> traverse (traverseTypeInExpr f) es
traverseTypeInExpr f (Cast e t) = Cast <$> traverseTypeInExpr f e <*> f t
traverseTypeInExpr f (StructCtor x ts fs) = StructCtor x <$> traverse (typeInTypeArgument f) ts <*> traverse (exprInStructFieldCtor (traverseTypeInExpr f)) fs
traverseTypeInExpr f (TypeAnnot t e) = TypeAnnot <$> f t <*> traverseTypeInExpr f e
traverseTypeInExpr f (TypeIf p e1 e2) = TypeIf <$> traverseTypeInTypePred f p <*> traverseTypeInExpr f e1 <*> traverseTypeInExpr f e2
traverseTypeInExpr f (TypePredExpr p) = TypePredExpr <$> traverseTypeInTypePred f p
traverseTypeInExpr f (TypeToExpr t) = TypeToExpr <$> f t
traverseTypeInExpr f (Lam isf xs mt e) = Lam isf <$> traverse (traverseTypeInLamParam f) xs <*> traverse f mt <*> traverseTypeInExpr f e
traverseTypeInExpr f e = plate (traverseTypeInExpr f) e

data Stmt name
  = Break Location
  | Continue Location
  | Expr (Expr name)
  | Let Bool (Binding name) (Expr name) -- TODO: Boolean to indicate recursive let is bad.
  | Return (Expr name)
  deriving (Functor, Foldable, Traversable)

-- TODO: This name is not correct, binding should be a pair composed of a variable and an expression
-- BindingOccurrence or LetLhs
data Binding name = Binding
  { _bindMut :: Mutability
  , _bindName :: Located name
  , _bindType :: Maybe (Type name)
  }
  deriving (Functor, Foldable, Traversable)

-- Finds only variables bound at the outermost level
varsDefinedInStmt :: Stmt name -> Maybe (Located name)
varsDefinedInStmt (Let _ var _) = Just (_bindName $ var)
varsDefinedInStmt _             = Nothing

traverseExprInStmt :: Traversal' (Stmt name) (Expr name)
traverseExprInStmt _ (Break l) = pure $ Break l
traverseExprInStmt _ (Continue l) = pure $ Continue l
traverseExprInStmt f (Expr e) = Expr <$> f e
traverseExprInStmt f (Let b bind e) = Let b bind <$> f e
traverseExprInStmt f (Return e) = Return <$> f e

typeInBinding :: Traversal' (Binding name) (Type name)
typeInBinding f (Binding m x t) = Binding m x <$> traverse f t

traverseTypeInStmt :: Traversal' (Stmt name) (Type name)
traverseTypeInStmt _ (Break l) = pure $ Break l
traverseTypeInStmt _ (Continue l) = pure $ Continue l
traverseTypeInStmt f (Expr e) = Expr <$> traverseTypeInExpr f e
traverseTypeInStmt f (Let b bind e) = Let b <$> typeInBinding f bind <*> traverseTypeInExpr f e
traverseTypeInStmt f (Return e) = Return <$> traverseTypeInExpr f e

traverseMatchRHSsInStmt :: Traversal' (Stmt name) (Expr name)
traverseMatchRHSsInStmt f = \ case
  Expr e       -> Expr <$> traverseMatchInExpr f e
  Let b bind e -> Let b bind <$> traverseMatchInExpr f e
  Return e     -> Return <$> traverseMatchInExpr f e
  stmt         -> pure stmt

data TypeParam name
  = TypeParam (Located name) Kind -- T or $S or @D
  | TypeParamQualify (Located name) (Maybe (Located name)) (Located name) -- T $S @D

data Function name
  = Function
  { _funSignature :: LSignature name
  , _funBody :: Expr name
  , _funIsSieve :: IsSieveFn
  }

data LamParam name
  = LamParam
  { _lamParamName :: Located name
  , _lamParamType :: Maybe (Type name)
  }
  deriving (Functor, Foldable, Traversable)

traverseTypeInLamParam :: Traversal' (LamParam name) (Type name)
traverseTypeInLamParam f (LamParam x mt) = LamParam x <$> traverse f mt

data FuncIdentifier name
  = FunctionId { _fiName :: name }
  | OperatorId { _fiName :: name }
  deriving (Functor, Foldable, Traversable)

data FuncParam name
  = FuncParam
  { _fnParamStyle :: ParamPassingStyle
  , _fnParamName :: Located name
  , _fnParamType :: Type name
  }
  | SelfParam
  { _fnParamStyle :: ParamPassingStyle
  , _fnParamLoc :: Location
  }
  deriving (Functor, Foldable, Traversable)

paramNameIfAny :: FuncParam name -> Maybe (Located name)
paramNameIfAny FuncParam{..} = Just _fnParamName
paramNameIfAny _             = Nothing

-- Function parameter used by typed and core representation.
-- Does not bind type to name explicitly but expects the name to have type already attached to it.
data SimpleFuncParam name
  = SimpleFuncParam ParamPassingStyle name
  deriving (Functor, Foldable, Traversable)

funcParamName :: SimpleFuncParam a -> a
funcParamName (SimpleFuncParam _ x) = x

data ParamPassingStyle
  = PassByValue
  | PassByRef
  deriving (Eq, Ord)

data Signature name
  = Signature
  { _sigName :: Located name
  , _sigIsPublic :: Bool
  , _sigTypeParameters :: Located [TypeParam name]
  , _sigParameters :: Located [FuncParam name]
  , _sigConstraints :: Located [TypePred name]
  , _sigReturnType :: Type name
  , _sigIsOperator :: Bool
  , _sigFixity :: Maybe (Located Fixity)
  , _sigEffect :: Maybe (Located (PolymorphicTypeWithEffect name))
  }

data TypeDef name
  = TypeDef
  { _tyDefName :: Located name
  , _tyDefIsPublic :: Bool
  , _tyDefParams :: Located [TypeParam name]
  , _tyDefResultKind :: Located Kind
  , _tyDefConstraints :: Located [TypePred name]
  , _tyDefType :: Type name
  }

data StructFieldDecl name
  = StructFieldDecl
  { _fieldDeclName :: Located T.Text -- field names can't be associated by structures
  , _fieldDeclType :: Type name
  }

data StructDecl name
  = StructDecl
  { _structDeclName :: Located name
  , _structDeclIsPublic :: Bool
  , _structDeclTypeParams :: [TypeParam name]
  , _structDeclFields :: [StructFieldDecl name]
  }

newtype Import
  = Import { _importName :: T.Text }

data StructImpl name
  = StructImpl
  { _structImplTypeParams :: Located [TypeParam name]
  , _structImplType :: Type name
  , _structImplBody :: [LFunction name]
  }

newtype Default name
  = Default
  { _defaultFields :: [Type name]
  }

data TopLevel name
  = TopFunction (LFunction name)
  | TopExtern (LSignature name)
  | TopTypeDef (LTypeDef name)
  | TopStructDecl (LStructDecl name)
  | TopImport LImport
  | TopStructImpl (LStructImpl name)
  | TopDefault (LDefault name)

data Program name
  = Program
  { _programTypeDefs :: [LTypeDef name]
  , _programStructDecls :: [LStructDecl name]
  , _programTopFunctions :: [LFunction name]
  , _programTopExterns :: [LSignature name]
  , _programImports :: [LImport]
  , _programStructImpls :: [LStructImpl name]
  , _programDefaults :: LDefault name
  }

-- Syntax constructs with attached location:
type LArraySlice name = Located (ArraySlice name)
type LFunction name = Located (Function name)
type LList name = Located (List name)
type LProgram name = Located (Program name)
type LSignature name = Located (Signature name)
type LTypeDef name = Located (TypeDef name)
type LStructDecl name = Located (StructDecl name)
type LImport  = Located Import
type LStructImpl name = Located (StructImpl name)
type LDefault name = Located (Default name)

type Module prog = (prog, String, [String])

makeLensesFor [("_funBody", "funBody")] ''Function
makeLensesFor [("_funSignature", "funSignature")] ''Function
makeLensesFor [("_structImplBody", "structImplBody")] ''StructImpl
makeLensesFor [("_defaultFields", "defaultFields")] ''Default
makeLensesFor [("_sigIsPublic", "sigIsPublic")] ''Signature
makeLensesFor [("_sigEffect", "sigEffect")] ''Signature

getTyParamNames :: TypeParam name -> [Located name]
getTyParamNames (TypeParam n _) = [n]
getTyParamNames (TypeParamQualify ty mstage dom) =
  [ty] ++ maybeToList mstage ++ [dom]

sigTypeParamVars :: Signature name -> [Located name]
sigTypeParamVars =
  concatMap getTyParamNames . unLocated . _sigTypeParameters

allSigTypeVars :: Eq name => Signature name -> [Located name]
allSigTypeVars Signature {..} =
  nubBy ((==) `on` unLocated) $ tyParamNames ++ typeNames
  where
    paramTypes = map _fnParamType $ unLocated _sigParameters
    predTypes = concatMap typesInTypePred $ unLocated _sigConstraints
    tyParamNames = concatMap getTyParamNames $ unLocated _sigTypeParameters
    typeNames = concatMap typeGetVarsWithLoc (_sigReturnType : paramTypes ++ predTypes)

signParams :: Signature name -> [(ParamPassingStyle, Located (Maybe name), Type name)] -- Nothing if self
signParams = map splitDecl . unLocated . _sigParameters
  where splitDecl (FuncParam ps lname ty) = (ps, fmap Just lname, ty)
        splitDecl (SelfParam ps loc) = (ps, Located loc Nothing, TSelf NoLocation)

implTypeParamVars :: StructImpl name -> [Located name]
implTypeParamVars =
  concatMap getTyParamNames . unLocated . _structImplTypeParams

traverseExprInStructImpl
  :: Traversal' (StructImpl name) (Expr name)
traverseExprInStructImpl
  = structImplBody . traverse . traverse . funBody

traverseExprInProgram :: Traversal' (Program name) (Expr name)
traverseExprInProgram f Program{..} =
  Program _programTypeDefs _programStructDecls <$>
    (_programTopFunctions & each.traverse.funBody %%~ f) <*>
    pure _programTopExterns <*>
    pure _programImports <*>
    (_programStructImpls & each.traverse.traverseExprInStructImpl %%~ f) <*>
    pure _programDefaults

traverseEffInTopLevel
  :: Traversal' (TopLevel name) (Maybe (Located (PolymorphicTypeWithEffect name)))
traverseEffInTopLevel f (TopFunction lfun)
  = TopFunction <$> traverse (traverseEffInFunction f) lfun
traverseEffInTopLevel f (TopExtern lsig)
  = TopExtern <$> traverse (sigEffect %%~ f) lsig
traverseEffInTopLevel f (TopStructImpl limpl)
  = TopStructImpl <$> traverse (structImplBody %%~ traverse (traverse (traverseEffInFunction f))) limpl
traverseEffInTopLevel _ toplevel
  = pure toplevel

traverseEffInFunction
  :: Traversal' (Function name) (Maybe (Located (PolymorphicTypeWithEffect name)))
traverseEffInFunction f
  = funSignature %%~ traverse (sigEffect %%~ f)

-- Assumes no variable overshadowing. Does not track variables bound in
-- block or by let-expressions. For instance "occurVarslet(x = 1 in x)" will
-- return {x}.
occurVars :: Uniquable a => Expr a -> UniqMap a
occurVars = para go
  where
    go (Var name)       _  = singletonUM' (unLocated name)
    go (Call _ fom _ _) ss = unionsUM (singletonUM' (unLocated (_fname fom)) : ss)
    go _                ss = unionsUM ss

getLValueTarget :: Expr a -> Either Location (Located (Maybe a)) -- Nothing if self
getLValueTarget = go NoLocation
  where
    go _ (Var lname)             = Right (fmap Just lname)
    go l Self                   = Right (Located l Nothing)
    go l (Select e _)           = go l e
    go l (Index e _)            = go l e
    go l (IndexStore e _)       = go l e
    go l (ExprLoc NoLocation e) = go l e
    go _ (ExprLoc l e)          = go l e
    go l (TypeAnnot _ e)        = go l e
    go l (Ascription e _)       = go l e
    go l (RefArg e)             = go l e
    go l _                      = Left l

viewForExpr :: Expr a -> Maybe (Located a, Expr a, Expr a, Expr a)
viewForExpr (ExprLoc _ e) = viewForExpr e
viewForExpr (TypeAnnot _ e) = viewForExpr e
viewForExpr (Ascription e _) = viewForExpr e
viewForExpr (For lx e1 e2 e3) = Just (lx, e1, e2, e3)
viewForExpr _ = Nothing


