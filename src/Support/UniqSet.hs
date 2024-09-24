{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Support.UniqSet
  (UniqSet,
   nullUS, emptyUS, deleteUS, memberUS, singletonUS,
   sizeUS, insertUS, unionUS, unionsUS, fromListUS
  )
  where

import Support.Unique

import qualified Data.IntSet as IntSet

type UniqSet a = IntSet.IntSet

wrap :: Uniquable a => (Int -> b) -> a -> b
wrap f u = f (uniqueGetInt (getUnique u))

wrapF :: (Functor f, Uniquable a) => (f Int -> b) -> f a -> b
wrapF f u = f (uniqueGetInt `fmap` getUnique `fmap` u)

nullUS :: UniqSet a -> Bool
nullUS = IntSet.null

emptyUS :: UniqSet a
emptyUS = IntSet.empty

deleteUS :: Uniquable a => a -> UniqSet a -> UniqSet a
deleteUS = wrap IntSet.delete

sizeUS :: UniqSet a -> Int
sizeUS = IntSet.size

memberUS :: Uniquable a => a -> UniqSet a -> Bool
memberUS = wrap IntSet.member

singletonUS :: Uniquable a => a -> UniqSet a
singletonUS = wrap IntSet.singleton

insertUS :: Uniquable a => a -> UniqSet a -> UniqSet a
insertUS = wrap IntSet.insert

unionUS :: UniqSet a -> UniqSet a -> UniqSet a
unionUS = IntSet.union

unionsUS :: [UniqSet a] -> UniqSet a
unionsUS = IntSet.unions

fromListUS :: Uniquable a => [a] -> UniqSet a
fromListUS = wrapF IntSet.fromList
