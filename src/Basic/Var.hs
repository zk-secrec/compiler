{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
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

module Basic.Var (
  Var,
  TyVar,
  MetaTyVar,
  Id,
  mkTyVar,
  mkMetaTyVar,
  mkId,
  isId,
  idType,
  idIsMutable,
  idSetMutable,
  isBuiltinVar,
  tyVarName,
  tyVarKind,
  isMetaTyVar,
  varName,
  isTyVar,
  nameLens,
  typeLens,
  typesInVar,
  varIsUntouchable,
) where

import Basic.Location
import Basic.Name
import Support.Pretty
import Support.Unique
import Typing.Kind
import Typing.Type

import Control.Lens.TH
import Control.Lens (Traversal')
import Control.DeepSeq (NFData, rnf)

data Var
  = TyVar
    { _name :: Name
    , _kind :: Kind
    }
  | MetaTyVar
    { _name :: Name
    , _kind :: Kind
    , _level :: Level
    }
  | Id
    { _name :: Name
    , _mutability :: Mutability
    , _type :: TypeScheme Var
    }

instance NFData Var where
  rnf !_ = ()

makeLensesFor [("_name", "nameLens"), ("_type", "typeLens")] ''Var

type TyVar = Var
type MetaTyVar = Var
type Id = Var

instance Eq Var where
  {-# INLINE (==) #-}
  (==) = eqVar

instance Ord Var where
  {-# INLINE compare #-}
  compare = compareVar

instance Pretty Var where
  pretty v@MetaTyVar{..} =
    pretty (nameOccName _name) <> "_" <> pretty (getUnique v) <> "{" <> pretty _level <> "}"
  pretty v = pprintName (_name v)

instance Uniquable Var where
  {-# INLINE getUnique #-}
  getUnique v = getUnique (_name v)

instance HasLocation Var where
  type UnLocated Var = Var
  location v = location (_name v)
  setLocation x l = x { _name = setLocation (_name x) l }
  stripLocation x = x

typesInVar :: Traversal' Var (Type Var)
typesInVar f (Id name mut (TForAll xs preds t)) =
    Id name mut <$> (
      TForAll xs <$> -- xs are type variables and thus must not contain types!
        traverse (traverseTypeInTypePred f) preds <*>
        f t)
typesInVar _ v = pure v

{-# INLINE isBuiltinVar #-}
isBuiltinVar :: Var -> Bool
isBuiltinVar = isBuiltin . _name

{-# INLINE isTyVar #-}
isTyVar :: Var -> Bool
isTyVar TyVar{} = True
isTyVar _ = False

{-# INLINE isMetaTyVar #-}
isMetaTyVar :: Var -> Bool
isMetaTyVar MetaTyVar{} = True
isMetaTyVar _ = False

{-# INLINE isId #-}
isId :: Var -> Bool
isId Id {} = True
isId _ = False

mkTyVar :: Name -> Kind -> Var
mkTyVar = TyVar

mkMetaTyVar :: Name -> Kind -> Level -> Var
mkMetaTyVar = MetaTyVar

mkId :: Name -> Mutability -> TypeScheme Var -> Var
mkId = Id

{-# INLINE varName #-}
varName :: Var -> Name
varName (TyVar x _) = x
varName (MetaTyVar x _ _) = x
varName (Id x _ _) = x

idType :: Var -> TypeScheme Var
idType = _type

idIsMutable :: Var -> Bool
idIsMutable = (== Mutable) . _mutability

idSetMutable :: Var -> Var
idSetMutable v = v { _mutability = Mutable }

tyVarName :: Var -> Name
tyVarName = _name

tyVarKind :: Var -> Kind
tyVarKind = _kind

varIsUntouchable :: Var -> Level -> Bool
varIsUntouchable MetaTyVar{..} contextLevel = _level < contextLevel
varIsUntouchable _ _ = True

----
-- Functions to help out inliner
----

{-# INLINE eqVar #-}
eqVar :: Var -> Var -> Bool
eqVar u v = varName u == varName v

{-# INLINE compareVar #-}
compareVar :: Var -> Var -> Ordering
compareVar u v = compare (_name u) (_name v)
