{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
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

module Typing.Constraints
  ( WantedConstraints(..)
  , Implication(..)
  , addWanted
  , andWanted
  , emptyWanted
  , addImplication
  , typePredInWantedConstraints
  ) where

import Typing.Type
import Support.Pretty
import Basic.Var

import Control.Lens (Traversal')

data WantedConstraints = WantedConstraints
  { _wanted :: [TypePred TyVar]
  , _implications :: [Implication]
  }

emptyWanted :: WantedConstraints
emptyWanted = WantedConstraints [] []

addWanted :: TypePred TyVar -> WantedConstraints -> WantedConstraints
addWanted p (WantedConstraints ps is) = WantedConstraints (p : ps) is

addImplication :: Implication -> WantedConstraints -> WantedConstraints
addImplication i (WantedConstraints ps is) = WantedConstraints ps (i : is)

andWanted :: WantedConstraints -> WantedConstraints -> WantedConstraints
andWanted (WantedConstraints ps is) (WantedConstraints ps' is') =
  WantedConstraints (ps ++ ps') (is ++ is')

data Implication = Implication
  { _implLevel  :: Level
  , _implGiven  :: [TypePred TyVar]
  , _implWanted :: WantedConstraints
  }

instance Pretty WantedConstraints where
  pretty (WantedConstraints ps is) =
    vcat $ map pretty ps ++ map pretty is

instance Pretty Implication where
  pretty Implication{..} =
    "implication:" $$ indent 2 (
      "level:" <+> pretty _implLevel $$
      "given:" <+> pretty _implGiven $$
      "wanted:" $$ indent 2 (pretty _implWanted))

typePredInWantedConstraints
  :: Traversal' WantedConstraints (TypePred TyVar)
typePredInWantedConstraints f (WantedConstraints ws is)
  = WantedConstraints <$> traverse f ws <*> traverse (typePredInImplication f) is

typePredInImplication
  :: Traversal' Implication (TypePred TyVar)
typePredInImplication f (Implication lev givens ws)
  = Implication lev <$> traverse f givens <*> typePredInWantedConstraints f ws

