{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Typing.Kind (
  Kind(..),
  mkKfun,
  unifyKinds,
  kindConvTo
) where

import Support.Pretty

{----------------
 -- Type Kinds --
 ----------------}

data Kind
  = KindDomain
  | KindStage
  | KindBool -- for effect system
  | KindNat
  | KindRing
  | KindUnqualified
  | KindStar
  | KindUnknown
  | KindFun Kind Kind
  | KindEffect
  deriving (Eq, Ord)

instance Pretty Kind where
  pretty = go never_prec
    where
      never_prec = 40
      fun_prec = 50

      go _ KindDomain = pretty "Domain"
      go _ KindStage = pretty "Stage"
      go _ KindBool = pretty "Bool"
      go _ KindNat = pretty "Nat"
      go _ KindRing = pretty "Ring"
      go _ KindUnqualified = pretty "Unqualified"
      go _ KindStar = pretty "Qualified"
      go _ KindUnknown = pretty "Unknown"
      go _ KindEffect = pretty "Effect"
      go p (KindFun k1 k2) = parensIf (p > fun_prec) $ go (fun_prec + 1) k1 <+> pretty "->" <+> go fun_prec k2

mkKfun :: [Kind] -> Kind -> Kind
mkKfun ks k = foldr KindFun k ks

kindConvTo :: Kind -> Kind -> Bool
kindConvTo KindUnknown _ = True
kindConvTo KindDomain KindDomain = True
kindConvTo KindStage KindStage = True
kindConvTo KindBool KindBool = True
kindConvTo KindNat KindNat = True
kindConvTo KindRing KindRing = True
kindConvTo KindUnqualified KindUnqualified = True
kindConvTo KindUnqualified KindStar = True
kindConvTo KindStar KindStar = True
kindConvTo (KindFun k1 k2) (KindFun k3 k4) = kindConvTo k2 k4 && kindConvTo k3 k1
kindConvTo _ _ = False

unifyKinds :: Kind -> Kind -> Maybe Kind
unifyKinds KindUnknown k2 = Just k2
unifyKinds k1 KindUnknown = Just k1
unifyKinds KindDomain KindDomain = Just KindDomain
unifyKinds KindStage KindStage = Just KindStage
unifyKinds KindBool KindBool = Just KindBool
unifyKinds KindNat KindNat = Just KindNat
unifyKinds KindRing KindRing = Just KindRing
unifyKinds KindStar KindUnqualified = Just KindStar
unifyKinds KindUnqualified KindStar = Just KindStar
unifyKinds KindUnqualified KindUnqualified = Just KindUnqualified
unifyKinds KindEffect KindEffect = Just KindEffect
unifyKinds KindStar KindStar = Just KindStar
unifyKinds (KindFun k1 k2) (KindFun k3 k4) = KindFun <$> unifyKinds k1 k3 <*> unifyKinds k2 k4
unifyKinds _ _ = Nothing
