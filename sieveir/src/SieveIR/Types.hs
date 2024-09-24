module SieveIR.Types where

import Data.Word (Word64)
import Numeric.Natural


data Version = Version Int Int Int

data Profile = CircuitArithmeticSimple | CircuitBooleanSimple

type Value = Natural

data Field
  = Field
  { characteristic :: Value
  , degree :: Int
  }

data Header
  = Header
  { version :: Version
  , profile :: Profile
  , field :: Field
  }

type Wire = Word64

data BinaryFunction = Mul | Add | And | Xor
data BinaryConstFunction = MulC | AddC
data UnaryFunction = Not

data Gate
  = Binary Wire BinaryFunction Wire Wire            -- ${x} <- {function} ( ${y}, ${z} );
  | BinaryConst Wire BinaryConstFunction Wire Value -- ${x} <- {function} ( ${y}, < {c} > );
  | Unary Wire UnaryFunction Wire                   -- ${x} <- {function} ( ${y} );
  | Copy Wire Wire                                  -- ${x} <- ${y};
  | Constant Wire Value                             -- ${x} <- < ${c} > ;
  | AssertZero Wire                                 -- assert_zero( ${y} );

data Counts
  = Counts
  { numWires :: Word64
  , numCommonInputs :: Word64
  , numShortWitness :: Word64
  }

data Relation
  = Relation
  { relationHeader :: Header
  , relationCounts :: Counts
  , gates :: [Gate]
  }

data Assignment = Assignment Wire Value

data Instance
  = Instance
  { instanceHeader :: Header
  , instanceCounts :: Counts
  , commonInputs :: [Assignment]
  }

data Witness
  = Witness
  { witnessHeader :: Header
  , witnessCounts :: Counts
  , shortWitness :: [Assignment]
  }

data Program
  = Program
  { relation :: Relation
  , witness :: Witness
  , instance_ :: Instance
  }
