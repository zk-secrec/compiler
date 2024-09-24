{-# LANGUAGE OverloadedStrings #-}

module Basic.Fixity
  ( Assoc(..)
  , Fixity(..)
  , Precedence(..)
  , defaultFixity
  ) where

import Support.Pretty

data Fixity = Fixity Assoc Integer

defaultFixity :: Fixity
defaultFixity = Fixity LeftAssoc 100

data Precedence name = Precedence {
    _fixity     :: Assoc,
    _precedence :: Integer,
    _operName   :: name
  }

instance Pretty a => Pretty (Precedence a) where
  pretty (Precedence a p n) = pretty a <+> pretty p <+> pretty n

data Assoc
  = NonAssoc
  | LeftAssoc
  | RightAssoc
  deriving (Eq, Ord)

instance Show Assoc where
  show = render . pretty

instance Pretty Assoc where
  pretty NonAssoc = "infix"
  pretty LeftAssoc = "infixl"
  pretty RightAssoc = "infixr"
