{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Basic.Name (
  Name,
  BuiltinInfo(..),
  mkName,
  nameUnique,
  nameLocation,
  nameOccName,
  pprintName,
  mkBuiltinName,
  isBuiltin,
  matchBuiltin,
  nameBuiltinInfo,
  uniqLens,
  mainFName
) where

import Basic.Location
import Support.Pretty
import Support.Unique

import Data.Text (Text)
import Control.Lens.TH

data BuiltinInfo
  = BuiltinAnd
  | BuiltinAdd
  | BuiltinBoolXor
  | BuiltinCircuitCall
  | BuiltinCircuitCallU
  | BuiltinDiv
  | BuiltinEq
  | BuiltinGe
  | BuiltinGetInstance
  | BuiltinGetPublic
  | BuiltinGetWitness
  | BuiltinGt
  | BuiltinLe
  | BuiltinLength
  | BuiltinLt
  | BuiltinMod
  | BuiltinModDiv
  | BuiltinMul
  | BuiltinNeg
  | BuiltinNeq
  | BuiltinOr
  | BuiltinPluginLT
  | BuiltinPluginLE
  | BuiltinPluginDiv
  | BuiltinPluginDivMod
  | BuiltinPluginBitextract
  | BuiltinPluginAssertPerm
  | BuiltinPluginAdd
  | BuiltinPluginMul
  | BuiltinPluginAddC
  | BuiltinPluginMulC
  | BuiltinPluginAddScalar
  | BuiltinPluginMulScalar
  | BuiltinPluginSum
  | BuiltinPluginProd
  | BuiltinPluginDotProd
  | BuiltinSub
  | BuiltinFieldBitWidth
  | BuiltinXor
  | BuiltinModInvert
  | BuiltinMakeWaksmanNetwork
  | BuiltinGetSortingPermutation
  | BuiltinPermutationSwitches
  | BuiltinUnslice
  | BuiltinFreeze
  | BuiltinThaw
  | BuiltinFlatten
  | BuiltinUnflatten
  | BuiltinIndexTensor
  | BuiltinIndexTensor1
  | BuiltinSize
  | BuiltinArrayToPost
  | BuiltinArrayToProver
  | BuiltinConst
  | BuiltinDbgPrint
  | BuiltinStringAppend
  | BuiltinToString
  | BuiltinDefaultValue
  | BuiltinChallenge
  | BuiltinAssert
  | BuiltinAssertEq
  | BuiltinAssertEqUintsBools
  | BuiltinAssertZero
  | BuiltinBitextractPreUint
  | BuiltinBitextractVecHelper
  | BuiltinMakeUnknown
  | BuiltinMakeNotUnknown
  | BuiltinUintNPreMatrixProd
  | BuiltinUintNPreMatrixProdI128
  deriving (Eq, Ord, Show)

data NameCategory
  = NameCategoryUser
  | NameCategoryBuiltin { _builtinInfo :: BuiltinInfo }

data Name = Name
  { _occ :: Text
  , _category :: NameCategory
  , _uniq :: !Unique
  , _loc :: !Location
  }

makeLensesFor [("_uniq", "uniqLens")] ''Name

instance HasLocation Name where
  type UnLocated Name = Name
  location = _loc
  setLocation x l = x { _loc = l }
  stripLocation x = x
  hasLocation _ = True

mkName :: Text -> Unique -> Location -> Name
mkName _occ _uniq _loc = Name{..}
  where _category = NameCategoryUser

mkBuiltinName :: Text -> BuiltinInfo -> Unique -> Location -> Name
mkBuiltinName occ info = Name occ (NameCategoryBuiltin info)

nameLocation :: Name -> Location
nameLocation = _loc

{-# INLINE nameOccName #-}
nameOccName :: Name -> Text
nameOccName = _occ

{-# INLINE isBuiltin #-}
isBuiltin :: Name -> Bool
isBuiltin Name { _category = NameCategoryBuiltin _ } = True
isBuiltin _ = False

matchBuiltin :: Name -> BuiltinInfo -> Bool
matchBuiltin Name { _category = NameCategoryBuiltin i } j = i == j
matchBuiltin _ _ = False

nameBuiltinInfo :: Name -> BuiltinInfo
nameBuiltinInfo = _builtinInfo . _category

instance Eq Name where
  {-# INLINE (==) #-}
  (==) = eqName

  {-# INLINE (/=) #-}
  (/=) = neqName

instance Pretty Name where
  pretty x = pretty (_occ x) <> underscore <> pretty (getUnique x)

instance Show Name where
  showsPrec d x = showsPrec d (_occ x)

instance Ord Name where
  {-# INLINE compare #-}
  compare = compareName

instance Uniquable Name where
  {-# INLINE getUnique #-}
  getUnique = nameUnique

pprintName :: Name -> Doc a
pprintName = pretty . _occ

mainFName :: Text
mainFName = "main"

----
-- Functions to help out inliner
----

{-# INLINE eqName #-}
eqName :: Name -> Name -> Bool
eqName (Name _ _ u _) (Name _ _ u' _) = u == u'

{-# INLINE neqName #-}
neqName :: Name -> Name -> Bool
neqName (Name _ _ u _) (Name _ _ u' _) = u /= u'

{-# INLINE compareName #-}
compareName :: Name -> Name -> Ordering
compareName (Name _ _ u _) (Name _ _ u' _) = compare u u'

{-# INLINE nameUnique #-}
nameUnique :: Name -> Unique
nameUnique (Name _ _ u _) = u
