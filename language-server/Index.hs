{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Index (SymbolInfo(..), Index, indexProgram, symbolLookup) where

import Basic.Location
import Basic.Var
import Basic.Name
import Control.Lens.Plated (universe)
import Data.Maybe (catMaybes, mapMaybe)
import Typing.Type
import Typing.Typing
import qualified Data.HashMap.Strict as HM
import Parser.Syntax
import Data.Graph (flattenSCCs)

data SymbolInfo
  = SymbolInfo
  { _type :: TypeScheme Var
  , _definition :: Location
  }

type Index = HM.HashMap Position SymbolInfo

symbolInfo :: Var -> SymbolInfo
symbolInfo var
  = SymbolInfo
  { _type = idType var
  , _definition = nameLocation (varName var)
  }

symbolLookup :: Position -> Index -> Maybe SymbolInfo
symbolLookup = HM.lookup

-- TODO: input should be a list of modules
-- TODO: type definitions
-- TODO: should goto support imports? E.g. "foo" in "use foo::*;"?
indexProgram :: TypedProgram -> Index
indexProgram TypedProgram{..} =
  HM.fromList $ catMaybes $ zipWith (\a b -> (, b) <$> a)
  (map (locationEnd . location) allVars)
  (map (symbolInfo . unLocated) allVars)
  where
    allVars = concatMap (getExprVars . _tFunBody)
      (flattenSCCs _tProgFunctions)

    getExprVars expr = mapMaybe getExprVar $ universe expr

    getExprVar (Var v) = Just v
    getExprVar (Call _ (Func tgt) _ _) = Just tgt
    getExprVar _ = Nothing
