{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Support.Unique (
  Unique,
  mkUnique,
  nextUnique,
  uniqueGetInt,
  Uniquable(..),
  Supply,
  unique,
  uniques,
  splitSupply,
  splitsSupply,
  newSupply
) where

import Support.Pretty
import Data.Word
import Data.IORef
import System.IO.Unsafe
import Data.IORef.Extra (writeIORef')

newtype Unique = U { uniqueGetInt :: Int }

instance Eq Unique where
  {-# INLINE (==) #-}
  U u == U v = u == v

  {-# INLINE (/=) #-}
  U u /= U v = u /= v

instance Ord Unique where
  {-# INLINE compare #-}
  compare (U u) (U v) = compare u v

mkUnique :: Int -> Unique
mkUnique = U

{-# INLINE nextUnique #-}
nextUnique :: Unique -> Unique
nextUnique (U x) = U (x + 1)

class Uniquable a where
  getUnique :: a -> Unique

instance Pretty Unique where
  pretty (U u) = pretty 'u' <> pretty u

instance Show Unique where
  showsPrec _ (U u) = showChar 'u' . shows u

instance Uniquable Unique where
  {-# INLINE getUnique #-}
  getUnique u = u

instance Uniquable Int where
  {-# INLINE getUnique #-}
  getUnique = U

instance Uniquable Integer where
  {-# INLINE getUnique #-}
  getUnique = U . fromInteger

instance Uniquable Word64 where
  {-# INLINE getUnique #-}
  getUnique = mkUnique . fromIntegral


data Supply =
  Supply
  { unique       :: {-# UNPACK #-} !Unique
  , _leftSupply  :: Supply
  , _rightSupply :: Supply
  }

uniques :: Supply -> [Unique]
uniques (Supply u _ r) = u : uniques r

splitSupply :: Supply -> (Supply, Supply)
splitSupply (Supply _ l r) = (l, r)

splitsSupply :: Supply -> [Supply]
splitsSupply (Supply _ l r) = l : splitsSupply r

type IOSupply = IORef Unique

newIOSupply :: IO IOSupply
newIOSupply = newIORef (U 0)

{-# INLINE getUniqueIO #-}
getUniqueIO :: IOSupply -> IO Unique
getUniqueIO s = do
    U u <- readIORef s
    writeIORef' s $! U (u + 1)
    return $! U u

getSupply :: IOSupply -> IO Supply
getSupply s = go
  where
    go = unsafeInterleaveIO $
      getUniqueIO s >>= \u ->
      go >>= \s1 ->
      go >>= \s2 ->
      return (Supply u s1 s2)

newSupply :: IO Supply
newSupply = newIOSupply >>= getSupply

