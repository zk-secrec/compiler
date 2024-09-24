{-# OPTIONS_GHC -fno-warn-orphans #-} -- IntMap Pretty instance

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Support.UniqMap (
  UniqMap,
  emptyUM,
  singletonUM,
  singletonUM',
  nullUM,
  lookupUM,
  insertUM,
  insertUM',
  insertWithUM,
  insertManyUM,
  memberUM,
  sizeUM,
  unionUM,
  unionWithUM,
  unionsUM,
  diffUM,
  intersectUM,
  mapUM,
  findUM,
  adjustUM,
  deleteUM,
  elemsUM,
  toListUM,
  fromAscListUM,
  fromListUM,
  fromListUM',
  fromListWithUM,
  findWithDefaultUM,
  unionsWithUM,
  mapMaybeUM,
  filterUM,
  partitionUM,
  keysUM
) where

import Support.Pretty
import Support.Unique
import qualified Data.IntMap.Strict as IntMap
import Control.Arrow (first)

type UniqMap a = IntMap.IntMap a

{-# INLINE wrap #-}
wrap :: Uniquable k => k -> (IntMap.Key -> a) -> a
wrap k f = f (uniqueGetInt (getUnique k))

emptyUM :: UniqMap a
emptyUM = IntMap.empty

nullUM :: UniqMap a -> Bool
nullUM = IntMap.null

sizeUM :: UniqMap a -> Int
sizeUM = IntMap.size

singletonUM :: Uniquable k => k -> a -> UniqMap a
singletonUM k v = wrap k $ \i -> IntMap.singleton i v

singletonUM' :: Uniquable a => a -> UniqMap a
singletonUM' v = singletonUM v v

{-# INLINE findUM #-}
findUM :: Uniquable k => k -> UniqMap a -> a
findUM k m = wrap k $ \i -> m IntMap.! i

{-# INLINE lookupUM #-}
lookupUM :: Uniquable k => k -> UniqMap a -> Maybe a
lookupUM k m = wrap k $ \i -> IntMap.lookup i m

{-# INLINE findWithDefaultUM #-}
findWithDefaultUM :: Uniquable k => a -> k -> UniqMap a -> a
findWithDefaultUM v k m = wrap k $ \i -> IntMap.findWithDefault v i m

{-# INLINE insertUM #-}
insertUM :: Uniquable k => k -> a -> UniqMap a -> UniqMap a
insertUM k v m = wrap k $ \i -> IntMap.insert i v m

{-# INLINE insertManyUM #-}
insertManyUM :: Uniquable k => [(k, a)] -> UniqMap a -> UniqMap a
insertManyUM [] um = um
insertManyUM [(k, v)] um = insertUM k v um
insertManyUM kvs um = fromListUM kvs `unionUM` um

{-# INLINE insertUM' #-}
insertUM' :: Uniquable a => a -> UniqMap a -> UniqMap a
insertUM' v m = wrap v $ \i -> IntMap.insert i v m

{-# INLINE deleteUM #-}
deleteUM :: Uniquable k => k -> UniqMap a -> UniqMap a
deleteUM k m = wrap k $ \i -> IntMap.delete i m

{-# INLINE adjustUM #-}
adjustUM :: Uniquable k => (a -> a) -> k -> UniqMap a -> UniqMap a
adjustUM f k m = wrap k $ \i -> IntMap.adjust f i m

{-# INLINE memberUM #-}
memberUM :: Uniquable k => k -> UniqMap a -> Bool
memberUM k m = wrap k $ \i -> IntMap.member i m

{-# INLINE fromListUM #-}
fromListUM :: Uniquable k => [(k, v)] -> UniqMap v
fromListUM kvs = IntMap.fromList $ map (first (uniqueGetInt.getUnique)) kvs

fromAscListUM :: Uniquable k => [(k, v)] -> UniqMap v
fromAscListUM kvs = IntMap.fromAscList $ map (first (uniqueGetInt.getUnique)) kvs

fromListUM' :: Uniquable v => [v] -> UniqMap v
fromListUM' vs = fromListUM [(v, v) | v <- vs]

fromListWithUM :: Uniquable k => (v -> v -> v) -> [(k, v)] -> UniqMap v
fromListWithUM f kvs = IntMap.fromListWith f $ map (first (uniqueGetInt.getUnique)) kvs

insertWithUM :: Uniquable k => (a -> a -> a) -> k -> a -> UniqMap a -> UniqMap a
insertWithUM f k v = wrap k $ \i -> IntMap.insertWith f i v

unionUM :: UniqMap a -> UniqMap a -> UniqMap a
unionUM = IntMap.union

unionWithUM :: (a -> a -> a) -> UniqMap a -> UniqMap a -> UniqMap a
unionWithUM = IntMap.unionWith

unionsWithUM :: (a -> a -> a) -> [UniqMap a] -> UniqMap a
unionsWithUM = IntMap.unionsWith

unionsUM :: Foldable f => f (UniqMap a) -> UniqMap a
unionsUM = IntMap.unions

diffUM :: UniqMap a -> UniqMap a -> UniqMap a
diffUM = IntMap.difference

intersectUM :: UniqMap a -> UniqMap a -> UniqMap a
intersectUM = IntMap.intersection

mapUM :: (a -> b) -> UniqMap a -> UniqMap b
mapUM = IntMap.map

elemsUM :: UniqMap a -> [a]
elemsUM = IntMap.elems

toListUM :: UniqMap a -> [(Int, a)]
toListUM = IntMap.toList

mapMaybeUM :: (a -> Maybe b) -> UniqMap a -> UniqMap b
mapMaybeUM = IntMap.mapMaybe

filterUM :: (a -> Bool) -> UniqMap a -> UniqMap a
filterUM = IntMap.filter

partitionUM :: (a -> Bool) -> UniqMap a -> (UniqMap a, UniqMap a)
partitionUM = IntMap.partition

keysUM :: UniqMap a -> [IntMap.Key]
keysUM = IntMap.keys

instance Pretty a => Pretty (IntMap.IntMap a) where
  pretty = pretty . IntMap.toList
