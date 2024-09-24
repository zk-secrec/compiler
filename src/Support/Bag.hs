{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Support.Bag (
  Bag,
  emptyBag,
  singletonBag,
  nullBag,
  sizeBag,
  concatBag,
  concatMapBag,
  elemBag,
  anyBag,
  allBag,
  unionBags,
  unionsBags,
  consBag,
  snocBag,
  mapBag,
  foldrBag,
  toListBag,
  fromListBag,
  zipWithPairsBag,
  orBag,
  andBag,
  filterBag
) where

import Support.Pretty

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Semigroup
import Data.Traversable
import Prelude hiding (foldr)

data Bag a
  = EmptyBag
  | SingletonBag a
  | TwoBags (Bag a) (Bag a)

instance Functor Bag where
  fmap = mapBag

instance Foldable Bag where
  foldr = foldrBag

instance Semigroup (Bag a) where
  a <> b = unionBags a b

instance Monoid (Bag a) where
  mempty = emptyBag
  mappend = unionBags
  mconcat = unionsBags

instance Traversable Bag where
  traverse _f EmptyBag         = pure EmptyBag
  traverse  f (SingletonBag x) = SingletonBag <$> f x
  traverse  f (TwoBags b1 b2)  = TwoBags <$> traverse f b1 <*> traverse f b2

instance Pretty a => Pretty (Bag a) where
  pretty = pretty . toListBag

emptyBag :: Bag a
emptyBag = EmptyBag

singletonBag :: a -> Bag a
singletonBag = SingletonBag

nullBag :: Bag a -> Bool
nullBag EmptyBag = True
nullBag _        = False

sizeBag :: Bag a -> Int
sizeBag EmptyBag = 0
sizeBag (SingletonBag _) = 1
sizeBag (TwoBags b1 b2) = sizeBag b1 + sizeBag b2

concatBag :: Bag (Bag a) -> Bag a
concatBag EmptyBag = EmptyBag
concatBag (SingletonBag b) = b
concatBag (TwoBags bs1 bs2) = concatBag bs1 `unionBags` concatBag bs2

concatMapBag :: (a -> Bag b) -> Bag a -> Bag b
concatMapBag f = go
  where
    go EmptyBag = EmptyBag
    go (SingletonBag x) = f x
    go (TwoBags b1 b2) = go b1 `unionBags` go b2

zipWithPairsBag :: (a -> b -> c) -> Bag a -> Bag b -> Bag c
zipWithPairsBag f = go
  where
    go EmptyBag         _                = EmptyBag
    go _                EmptyBag         = EmptyBag
    go (TwoBags b1 b2)  b                = TwoBags (go b1 b) (go b2 b)
    go b                (TwoBags b1 b2)  = TwoBags (go b b1) (go b b2)
    go (SingletonBag x) (SingletonBag y) = SingletonBag (f x y)

elemBag :: Eq a => a -> Bag a -> Bool
elemBag _x EmptyBag = False
elemBag  x (SingletonBag y) = x == y
elemBag  x (TwoBags b1 b2) = elemBag x b1 || elemBag x b2

anyBag :: (a -> Bool) -> Bag a -> Bool
anyBag _p EmptyBag = False
anyBag  p (SingletonBag x) = p x
anyBag  p (TwoBags b1 b2) = anyBag p b1 || anyBag p b2

orBag :: Bag Bool -> Bool
orBag EmptyBag = False
orBag (SingletonBag p) = p
orBag (TwoBags b1 b2) = orBag b1 || orBag b2

allBag :: (a -> Bool) -> Bag a -> Bool
allBag _p EmptyBag = True
allBag  p (SingletonBag x) = p x
allBag  p (TwoBags b1 b2) = allBag p b1 && allBag p b2

andBag :: Bag Bool -> Bool
andBag EmptyBag = True
andBag (SingletonBag p) = p
andBag (TwoBags b1 b2) = andBag b1 && andBag b2

unionsBags :: [Bag a] -> Bag a
unionsBags = foldr unionBags emptyBag

unionBags :: Bag a -> Bag a -> Bag a
unionBags EmptyBag b = b
unionBags b EmptyBag = b
unionBags b1 b2 = TwoBags b1 b2

consBag :: a -> Bag a -> Bag a
consBag x b = singletonBag x `unionBags` b

snocBag :: Bag a -> a -> Bag a
snocBag b x = b `unionBags` singletonBag x

mapBag :: (a -> b) -> Bag a -> Bag b
mapBag _f EmptyBag         = EmptyBag
mapBag  f (SingletonBag x) = SingletonBag (f x)
mapBag  f (TwoBags b1 b2)  = TwoBags (mapBag f b1) (mapBag f b2)

foldrBag :: (a -> b -> b) -> b -> Bag a -> b
foldrBag _f z EmptyBag         = z
foldrBag  f z (SingletonBag x) = f x z
foldrBag  f z (TwoBags b1 b2)  = foldrBag f (foldrBag f z b2) b1

toListBag :: Bag a -> [a]
toListBag = foldrBag (:) []

fromListBag :: [a] -> Bag a
fromListBag = foldr consBag EmptyBag

filterBag :: (a -> Bool) -> Bag a -> Bag a
filterBag p = go
  where
    go EmptyBag = EmptyBag
    go (SingletonBag x) = if p x then SingletonBag x else EmptyBag
    go (TwoBags b1 b2) = unionBags (go b1) (go b2)
