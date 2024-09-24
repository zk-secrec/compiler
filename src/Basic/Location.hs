{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
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

module Basic.Location
    (Position(..),
     Location(..),
     HasLocation(..),
     Located(..),
     movePos, unLocated, mkLocation,
     extendLeft, extendRight,
     joinLocations, noLoc,
     withLoc, ignoreLoc, wrapLoc,
     locationStart, locationEnd
    )
    where

import Control.Applicative
import Data.Hashable (Hashable (..))
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldr)
import Support.Pretty

data Position
  = Position {
    _posFilename :: String,
    _posLine     :: !Int,
    _posCol      :: !Int
  } deriving (Eq, Ord)

instance Pretty Position where
  pretty pos =
    pretty (_posFilename pos) <> colon <>
    pretty (_posLine pos) <> colon <>
    pretty (_posCol pos)

instance Hashable Position where
  hashWithSalt salt Position{..} =
    hashWithSalt salt _posFilename
    `hashWithSalt` _posLine
    `hashWithSalt` _posCol

movePos :: Position -> Char -> Position
movePos (Position f l _) '\n' = Position f (l + 1) 1
movePos (Position f l c) _    = Position f l (c + 1)

data Location
  = NoLocation
  | Location {
    _locFilename  :: String,
    _locFirstLine :: !Int,
    _locFirstCol  :: !Int,
    _locLastLine  :: !Int,
    _locLastCol   :: !Int
  }
  deriving (Eq, Ord, Show)

instance Pretty Location where
  pretty NoLocation = "<no location info>"
  pretty Location{..}
    | isMultiLine = pretty _locFilename <> colon <> lineRange
    | otherwise = pretty _locFilename <> colon <> lineRange <> colon <> colRange
    where
      isMultiLine = _locLastLine - _locFirstLine > 1
      lineRange
        | not isMultiLine = pretty _locFirstLine
        | otherwise = pretty _locFirstLine <> "-" <> pretty _locLastLine
      colRange
        | _locLastCol - _locFirstCol <= 1 = pretty _locFirstCol
        | otherwise = pretty _locFirstCol <> "-" <> pretty _locLastCol

class HasLocation a where
  type UnLocated a

  location :: a -> Location
  setLocation :: UnLocated a -> Location -> a
  stripLocation :: a -> UnLocated a

  hasLocation :: a -> Bool
  hasLocation x = case location x of
    NoLocation -> False
    _          -> True

  modifyLocation :: (Location -> Location) -> a -> a
  modifyLocation f x = stripLocation x `setLocation` f (location x)

extendLeft :: HasLocation a => Location -> a -> a
extendLeft l = modifyLocation (l `joinLocations`)

extendRight :: HasLocation a => a -> Location -> a
extendRight x l = modifyLocation (`joinLocations` l) x

locationStart :: Location -> Maybe Position
locationStart NoLocation = Nothing
locationStart Location{..}
  = Just $ Position
  { _posFilename = _locFilename
  , _posLine = _locFirstLine
  , _posCol = _locFirstCol
  }

locationEnd :: Location -> Maybe Position
locationEnd NoLocation = Nothing
locationEnd Location{..}
  = Just $ Position
  { _posFilename = _locFilename
  , _posLine = _locLastLine
  , _posCol = _locLastCol
  }

mkLocation :: Position -> Position -> Location
mkLocation startPos endPos = Location {
    _locFilename  = _posFilename startPos,
    _locFirstLine = _posLine startPos,
    _locFirstCol  = _posCol startPos,
    _locLastLine  = _posLine endPos,
    _locLastCol   = _posCol endPos
  }

joinLocations :: Location -> Location -> Location
joinLocations NoLocation loc' = loc'
joinLocations loc NoLocation = loc
joinLocations loc loc' = loc {
      _locLastLine = _locLastLine loc',
      _locLastCol  = _locLastCol loc'
    }

instance HasLocation Location where
  type UnLocated Location = Location
  location l = l
  setLocation _ l = l
  stripLocation _ = NoLocation
  hasLocation _ = True


data Located a = Located Location a
  deriving (Eq, Functor, Foldable, Traversable)

instance HasLocation (Located a) where
  type UnLocated (Located a) = a
  location (Located l _) = l
  setLocation x l = Located l x
  stripLocation (Located _ x) = x
  hasLocation _ = True

instance (HasLocation a, HasLocation b) => HasLocation (Either a b) where
  type UnLocated (Either a b) = Either (UnLocated a) (UnLocated b)

  location = either location location
  setLocation (Left x) = Left . setLocation x
  setLocation (Right x) = Right . setLocation x
  stripLocation (Left x) = Left (stripLocation x)
  stripLocation (Right x) = Right (stripLocation x)
  hasLocation = either hasLocation hasLocation

instance Pretty a => Pretty (Located a) where
  pretty (Located _ a) = pretty a

instance Show a => Show (Located a) where
  show (Located pos a) = concat ["(Located (", show pos, ") (", show a, "))"]

unLocated :: Located a -> a
unLocated (Located _ x) = x

noLoc :: a -> Located a
noLoc = Located NoLocation

withLoc :: Functor f => (Location -> a -> f b) -> Located a -> f (Located b)
withLoc f (Located loc x) = Located loc <$> f loc x

wrapLoc :: (a -> b) -> Located a -> Located b
wrapLoc f (Located loc x) = Located loc (f x)

ignoreLoc :: Functor f => (a -> f b) -> Located a -> f (Located b)
ignoreLoc f (Located loc x) = Located loc <$> f x
