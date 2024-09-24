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

module Typing.StructEnv
  ( StructFieldInfo(..)
  , StructEnv(..)
  , StructsEnv
  , tryGetFieldTypes
  , tryGetFieldPos
  ) where


import Basic.Location
import Basic.Name
import Basic.Var
import Support.UniqMap
import Typing.Type
import Parser.Syntax (Selector(..))

import qualified Data.Text as T
import qualified Data.Map as M
import Data.List (sortOn)
import Control.Exception (assert)
import GHC.Stack (HasCallStack)

data StructFieldInfo
  = StructFieldInfo
  { _fieldName  :: T.Text
  , _fieldPos   :: Int
  , _fieldType  :: Type TyVar
  }

data StructEnv
  = StructEnv
  { _structName :: Name
  , _structLocation :: Location
  , _structType :: TypeScheme TyVar
  , _structFields :: M.Map T.Text StructFieldInfo
  , _structFinalizer :: Maybe Name
  }

type StructsEnv = UniqMap StructEnv

-- Get structure field types sorted by their position.
fieldsInOrder :: StructEnv -> [Type TyVar]
fieldsInOrder = map _fieldType . sortOn _fieldPos . M.elems . _structFields

-- | Return field types of tuple-like types (structs, tuples, unit type).
-- Performs type substitution as needed.
tryGetFieldTypes :: HasCallStack => StructsEnv -> Type TyVar -> Maybe [Type TyVar]
tryGetFieldTypes senv = \case
  TQualify t' _ _ -> tryGetFieldTypes senv t'
  TTuple ts -> return ts
  TVar x _ _ -> fieldsInOrder <$> lookupUM x senv
  (TApp (TVar x _ _) ts _) -> do
    senv@StructEnv{..} <- lookupUM x senv
    let TForAll vs _ _ = _structType
    assert (length vs == length ts) $ do
      let subst = fromListUM $ zip vs ts
      let fieldTypes = map (subType subst) $ fieldsInOrder senv
      return fieldTypes
  _ -> Nothing

tryGetFieldPos :: StructsEnv -> Type TyVar -> Selector -> Maybe Int
tryGetFieldPos senv ty sel = go ty
  where
    go (TQualify t' _ _) = go t'
    go (TTuple _) = do
      SelectIndex i <- return sel
      return i
    go (TVar x _ _) = do
      StructEnv{..} <- lookupUM x senv
      SelectField fname <- return sel
      StructFieldInfo{..} <- M.lookup fname _structFields
      return _fieldPos
    go (TApp (TVar x _ _) _ _) = do
      StructEnv{..} <- lookupUM x senv
      SelectField fname <- return sel
      StructFieldInfo{..} <- M.lookup fname _structFields
      return _fieldPos
    go _ = Nothing
