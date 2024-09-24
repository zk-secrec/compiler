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

module CCC.Syntax (
  Versioned(..),
  extractVersion,
  CCCPlugin(..),
  CCCPred(..),
  CCCType(..),
  CCCChallenge(..),
  CCCConversion(..),
  CCCConstraintArg(..),
  CCCConstraint(..),
  CCCConstraintBlock(..),
  CCC(..)
) where

import Basic.Location
import Support.Pretty
-- import Support.UniqMap
-- import Support.Unique (Uniquable)
-- import Typing.Type

-- import Control.Lens hiding (List)
-- import Data.Function
import Data.Char
import qualified Data.Text as T


data Versioned name = Versioned {
    _versionedName :: name,
    _versionedVer :: [Int]
  }

instance (Pretty name) => Pretty (Versioned name) where
  
  pretty Versioned{..}
    | null _versionedVer
      = pretty _versionedName
    | otherwise
      = pretty _versionedName <> "_v" <> hcat (punctuate "." (fmap pretty _versionedVer))

extractVersion
  :: T.Text -> Versioned T.Text
extractVersion text
  = case T.splitOn "_v" text of
      [prefix, suffix]
        | not (T.null prefix) && not (T.null suffix) && all (\ part -> not (T.null part) && T.all isDigit part) verparts
          -> Versioned 
             { _versionedName = prefix
             , _versionedVer = fmap (read . T.unpack) verparts
             }
        where
          verparts
            = T.splitOn "." suffix
      _ -> Versioned 
           { _versionedName = text
           , _versionedVer = []
           }

type TypeIx = Int

newtype CCCPlugin name
  = CCCPlugin (Located (Versioned name))

data CCCPred
  = CCCLT (Located Integer)
  | CCCGT (Located Integer)
  | CCCEQ (Located Integer)
  | CCCMersenne
  | CCCProth
  | CCCPow2

data CCCType name
  = CCCField { _cccFieldPreds :: [Located CCCPred] }
  | CCCExtField 
    { _cccBaseFields :: [Located TypeIx]
    , _cccDegPreds :: [Located CCCPred]
    , _cccPolPreds :: [Located CCCPred]
    }
  | CCCRing { _cccWidthPreds :: [Located CCCPred] }
  | CCCPluginType (Located name)

data CCCChallenge
  = CCCChallenge (Located TypeIx)

data CCCConversion
  = CCCConversion (Located TypeIx) (Located TypeIx)

data CCCConstraintArg name
  = CCCNameArg (Located name)
  | CCCPredArg (Located CCCPred)
  | CCCNumArg (Located Integer)

data CCCConstraint name
  = CCCConstraint [Located (CCCConstraintArg name)]

data CCCConstraintBlock name
  = CCCConstraintBlock (Located name) [Located (CCCConstraint name)]

data CCC name
  = CCC
    { _cccVersion :: Located (Located Int , Located Int , Located Int)
    , _cccPlugins :: [Located (CCCPlugin name)]
    , _cccTypes :: [Located (CCCType name)]
    , _cccChallenges :: [Located CCCChallenge]
    , _cccConversions :: [Located CCCConversion]
    , _cccConstraints :: [Located (CCCConstraintBlock name)]
    }


