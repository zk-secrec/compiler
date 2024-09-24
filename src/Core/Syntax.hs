{-# LANGUAGE DeriveTraversable #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Core.Syntax (
  CorePat'(..),
  CoreLoop'(..),
  CoreBind'(..),
  CoreLet'(..),
  CoreExpr'(..),
  CoreTopExtern(..),
  CoreTopFunction(..),
  CoreTopConstant(..),
  CoreStructImpl(..),
  CoreProgram(..),
  CoreOffset'(..),
  IsSieveFn(..),
  IsLambda(..),
  IsVectorized(..),
  SimpleFuncParam(..),
  ParamPassingStyle(..),
  CorePat,
  CoreBind,
  CoreLet,
  CoreLoop,
  CoreExpr,
  CoreOffset,
  exprInCoreLet,
  letInCoreExpr,
  typeInCoreExpr,
  varsInCoreExpr,
  funcParamName,
  litsInCoreProgram,
  definedVarsInCoreProgram,
)
where

import Basic.Var
import Parser.Syntax

import Data.Graph (SCC(..))
import Basic.Location
import Control.Lens (Traversal', both, Lens', _1)

newtype CorePat' a = CorePat [a]
  deriving (Functor, Foldable, Traversable)

data CoreBind' a = CoreBind Bool (CorePat' a) (CoreExpr' a)
  deriving (Functor, Foldable, Traversable)

data CoreLet' a = CoreLet [CoreBind' a] [a]
  deriving (Functor, Foldable, Traversable)

-- the Bool denotes whether the bind is recursive

-- Lets evaluate to n-tuple of variables where n >= 1.
-- Tuples constructed this way must be irrefutably pattern
-- matched to n-tuples of the same n.

data CoreLoop' a
  = CoreForRange
  { _loopVar         :: a
  , _loopBegin       :: a
  , _loopEnd         :: a
  , _loopBody        :: CoreLet' a
  }
  | CoreForExpr
  { _loopVar         :: a
  , _loopBegin       :: a
  , _loopEnd         :: a
  , _loopBody        :: CoreLet' a
  }
  | CoreForever
  { _loopBody        :: CoreLet' a
  }
  deriving (Functor, Foldable, Traversable)

data CoreOffset' a
  = COffTuple !Int               -- ^ Index into tuple
  | COffStruct !Int              -- ^ Index into struct
  | COffDynamic !(ArraySlice a)  -- ^ Slice/index into array
  | COffKey !a                   -- ^ Offset into store data type
  deriving (Functor, Foldable, Traversable)

data CoreExpr' a
  = CeDbgAssert a Location (Maybe (CoreLet' a))
  | CeDbgAssertEq a a Location (Maybe (CoreLet' a))
  | CeVar a
  | CeLam IsSieveFn [a] (CoreLet' a)
  | CeLit Constant
  | CeLet (CoreLet' a)
  | CeCall IsVectorized a [Type a] [a] Location
  | CeCast a (Type a)
  | CeLoop (CoreLoop' a)
  | CeZip [(a, a)] (CoreLet' a) -- zip x_1 in xs_1, ..., x_n in xs_n with { ... }
  | CeIfThenElse a (CoreLet' a) (CoreLet' a)
  | CeMatch a [(Integer, a)] a [a] -- we assume that the rhss have been defined in lambda expressions and bound to variables before
                                   -- the 3rd argument is the default case
                                   -- the last argument is the list of free variables that the lambda expressions expect as arguments (the same list must be expected by all of the lambda expressions)
  | CeStore a [CoreOffset' a] a
  | CeStoreCtor [(a, a)]
  | CeLoad a [CoreOffset' a]
  | CeRef a [CoreOffset' a]
  | CeList (List a)
  | CeTuple [a]
  | CeStructCtor a [Type a] [a]
  | CeWire a (CoreLet' a)
  | CeTrace Location String (CoreLet' a)
  | CeTypeIf (TypePred a) (CoreLet' a) (CoreLet' a)
  | CeTypeToExpr (Type a)
  | CeContinue Int
  | CeBreak Int
  | CeBot -- Undefined bottom value, should never be evaluated. Can be assumed to not be introduced.
  deriving (Functor, Foldable, Traversable)

type CorePat = CorePat' Var
type CoreBind = CoreBind' Var
type CoreLet = CoreLet' Var
type CoreLoop = CoreLoop' Var
type CoreExpr = CoreExpr' Var
type CoreOffset = CoreOffset' Var

litsInCoreExpr :: Traversal' (CoreExpr' a) Constant
litsInCoreExpr f (CeLit c) = CeLit <$> f c
litsInCoreExpr f e = letInCoreExpr (exprInCoreLet (litsInCoreExpr f)) e

-- Variables that immediately occur in the expression.
-- Does NOT traverse nested variables or the ones that reside under let.
varsInCoreExpr :: Traversal' (CoreExpr' a) a
varsInCoreExpr f (CeDbgAssert x l mlt) = CeDbgAssert <$> f x <*> pure l <*> pure mlt
varsInCoreExpr f (CeDbgAssertEq x y l mlt) = CeDbgAssertEq <$> f x <*> f y <*> pure l <*> pure mlt
varsInCoreExpr f (CeVar x) = CeVar <$> f x
varsInCoreExpr f (CeCall iv x ts xs l) = CeCall iv <$> f x <*> pure ts <*> traverse f xs <*> pure l
varsInCoreExpr f (CeCast x t) = CeCast <$> f x <*> pure t
varsInCoreExpr f (CeLoop loop) = CeLoop <$> case loop of
  CoreForRange x y z lt -> CoreForRange <$> f x <*> f y <*> f z <*> pure lt
  CoreForExpr x y z lt -> CoreForExpr <$> f x <*> f y <*> f z <*> pure lt
  CoreForever lt -> pure $ CoreForever lt
varsInCoreExpr f (CeZip ps lt) = CeZip <$> traverse (both f) ps <*> pure lt
varsInCoreExpr f (CeIfThenElse x tlt flt) = CeIfThenElse <$> f x <*> pure tlt <*> pure flt
varsInCoreExpr f (CeMatch x cases defcase xs) = CeMatch <$> f x <*> pure cases <*> pure defcase <*> traverse f xs
varsInCoreExpr f (CeStoreCtor kvs) = CeStoreCtor <$> traverse (both f) kvs
varsInCoreExpr f (CeStore x is y) = CeStore <$> f x <*> traverse (traverse f) is <*> f y
varsInCoreExpr f (CeLoad x is) = CeLoad <$> f x <*> traverse (traverse f) is
varsInCoreExpr f (CeRef x is) = CeRef <$> f x <*> traverse (traverse f) is
varsInCoreExpr f (CeLam is xs lt) = CeLam is <$> traverse f xs <*> pure lt
varsInCoreExpr f (CeList list) = CeList <$> traverse f list
varsInCoreExpr f (CeTuple xs) = CeTuple <$> traverse f xs
varsInCoreExpr f (CeWire x lt) = CeWire <$> f x <*> pure lt
varsInCoreExpr _ e = pure e

definedVarsInCoreExpr :: Traversal' (CoreExpr' a) a
definedVarsInCoreExpr f (CeDbgAssert x l mlt) = CeDbgAssert x l <$> traverse (definedVarsInLet f) mlt
definedVarsInCoreExpr f (CeDbgAssertEq x y l mlt) = CeDbgAssertEq x y l <$> traverse (definedVarsInLet f) mlt
definedVarsInCoreExpr f (CeLam is xs lt) = CeLam is <$> traverse f xs <*> definedVarsInLet f lt
definedVarsInCoreExpr f (CeWire x lt) = CeWire x <$> definedVarsInLet f lt
definedVarsInCoreExpr f (CeIfThenElse x tlt flt) = CeIfThenElse x <$> definedVarsInLet f tlt <*> definedVarsInLet f flt
definedVarsInCoreExpr f (CeTypeIf p tlt flt) = CeTypeIf p <$> definedVarsInLet f tlt <*> definedVarsInLet f flt
definedVarsInCoreExpr f (CeLoop loop) = CeLoop <$> case loop of
  CoreForRange x y z lt -> CoreForRange <$> f x <*> pure y <*> pure z <*> definedVarsInLet f lt
  CoreForExpr x y z lt -> CoreForExpr <$> f x <*> pure y <*> pure z <*> definedVarsInLet f lt
  CoreForever lt -> CoreForever <$> definedVarsInLet f lt
definedVarsInCoreExpr f (CeZip ps lt) = CeZip <$> traverse (_1 f) ps <*> definedVarsInLet f lt
definedVarsInCoreExpr _ e = pure e

definedVarsInLet :: Traversal' (CoreLet' a) a
definedVarsInLet f (CoreLet binds body) = CoreLet <$> traverse (definedVarsInCoreBind f) binds <*> pure body

definedVarsInCoreBind :: Traversal' (CoreBind' a) a
definedVarsInCoreBind f (CoreBind b (CorePat xs) rhs) = CoreBind b <$> (CorePat <$> traverse f xs) <*> definedVarsInCoreExpr f rhs

-- Types that immediate occur in the expression.
typeInCoreExpr :: Traversal' (CoreExpr' a) (Type a)
typeInCoreExpr f (CeCall iv g ts xs l) = CeCall iv g <$> traverse f ts <*> pure xs <*> pure l
typeInCoreExpr f (CeTypeToExpr ty) = CeTypeToExpr <$> f ty
typeInCoreExpr f (CeTypeIf ty tlt flt) =
  CeTypeIf <$> traverseTypeInTypePred f ty <*> pure tlt <*> pure flt
typeInCoreExpr f (CeCast x t) = CeCast x <$> f t
typeInCoreExpr f (CeStructCtor s ts xs) = CeStructCtor s <$> traverse f ts <*> pure xs
typeInCoreExpr _ e = pure e

exprInCoreLet :: Traversal' (CoreLet' a) (CoreExpr' a)
exprInCoreLet f (CoreLet bs xs) = CoreLet <$> traverse doBind bs <*> pure xs
  where doBind (CoreBind m pat e) =  CoreBind m pat <$> f e

letInCoreExpr :: Traversal' (CoreExpr' a) (CoreLet' a)
letInCoreExpr f (CeDbgAssert x l mlt) = CeDbgAssert x l <$> traverse f mlt
letInCoreExpr f (CeDbgAssertEq x y l mlt) = CeDbgAssertEq x y l <$> traverse f mlt
letInCoreExpr f (CeLam is xs lt) = CeLam is xs <$> f lt
letInCoreExpr f (CeLet lt) = CeLet <$> f lt
letInCoreExpr f (CeIfThenElse x tlt flt) = CeIfThenElse x <$> f tlt <*> f flt
letInCoreExpr f (CeWire x lt) = CeWire x <$> f lt
letInCoreExpr f (CeTypeIf p tlt flt) = CeTypeIf p <$> f tlt <*> f flt
letInCoreExpr f (CeLoop loop) = CeLoop <$> case loop of
  CoreForRange x y z lt -> CoreForRange x y z <$> f lt
  CoreForExpr x y z lt -> CoreForExpr x y z <$> f lt
  CoreForever lt -> CoreForever <$> f lt
letInCoreExpr f (CeZip ps lt) = CeZip ps <$> f lt
letInCoreExpr _ e = pure e

data IsLambda = IsLambda | NotLambda -- does this top-level function originate from a lambda
  deriving Eq

data CoreTopFunction = CoreTopFunction
  { _coreFunName :: Id
  , _coreFunArgs :: [SimpleFuncParam Id]
  , _coreFunBody :: CoreLet
  , _coreFunIsSieve :: IsSieveFn
  , _coreFunIsLambda :: IsLambda
  }

data CoreTopExtern = CoreTopExtern
  { _coreExtName :: Id
  , _coreExtArgs :: [SimpleFuncParam Id]
  }

definedVarsInCoreTopFunction :: Traversal' CoreTopFunction Id
definedVarsInCoreTopFunction f (CoreTopFunction name args lt is il) =
    CoreTopFunction <$> f name <*> traverse (traverse f) args <*> definedVarsInLet f lt <*> pure is <*> pure il

definedVarsInCoreTopExtern :: Traversal' CoreTopExtern Id
definedVarsInCoreTopExtern f (CoreTopExtern name args) =
    CoreTopExtern <$> f name <*> traverse (traverse f) args

data CoreTopConstant = CoreTopConstant
  { _coreConstName :: Id
  , _coreConstDef  :: CoreLet
  }

data CoreStructImpl = CoreStructImpl
  { _coreImplType :: Type Var
  , _coreImplMethods :: [CoreTopFunction]
  }

data CoreProgram = CoreProgram
  { _coreExterns :: [CoreTopExtern]
  , _coreFunctions :: [SCC CoreTopFunction]
  , _coreStructImpls :: [CoreStructImpl]
  }

coreFunBody :: Lens' CoreTopFunction CoreLet
coreFunBody f (CoreTopFunction x as lt is il) = (\ lt -> CoreTopFunction x as lt is il) <$> f lt

litsInCoreStructImpl :: Traversal' CoreStructImpl Constant
litsInCoreStructImpl f (CoreStructImpl t fs) = CoreStructImpl t <$> traverse (coreFunBody (exprInCoreLet (litsInCoreExpr f))) fs

litsInCoreProgram :: Traversal' CoreProgram Constant
litsInCoreProgram f (CoreProgram es fs impls) = CoreProgram es <$> traverse (traverse (coreFunBody (exprInCoreLet (litsInCoreExpr f)))) fs
                                                               <*> traverse (litsInCoreStructImpl f) impls

definedVarsInCoreStructImpl :: Traversal' CoreStructImpl Id
definedVarsInCoreStructImpl f (CoreStructImpl t fs) = CoreStructImpl t <$> traverse (definedVarsInCoreTopFunction f) fs

definedVarsInCoreProgram :: Traversal' CoreProgram Id
definedVarsInCoreProgram f (CoreProgram es fs impls) = CoreProgram <$> traverse (definedVarsInCoreTopExtern f) es
                                                                   <*> traverse (traverse (definedVarsInCoreTopFunction f)) fs
                                                                   <*> traverse (definedVarsInCoreStructImpl f) impls
