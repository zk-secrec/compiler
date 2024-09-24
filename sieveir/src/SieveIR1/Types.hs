module SieveIR1.Types where

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

data IteratorExpr = IEConst Word64
                  | IEVar String
                  | IEAdd IteratorExpr IteratorExpr
                  | IESub IteratorExpr IteratorExpr
                  | IEMul IteratorExpr IteratorExpr
data IteratorRange = IE IteratorExpr | IERange IteratorExpr IteratorExpr

data LoopAnonCall = LoopAnonCall [IteratorExpr] [IteratorExpr] Word64 Word64 [Gate]
                    -- ies1 <- @anon_call(ies2, @instance: n1, @short_witness: n2) ... @end

data Gate
  = Binary !Wire BinaryFunction !Wire !Wire                 --  ${x} <- {function} ( ${y}, ${z} );
  | BinaryConst !Wire BinaryConstFunction !Wire !Value      --  ${x} <- {function} ( ${y}, < {c} > );
  | Unary !Wire UnaryFunction !Wire                         --  ${x} <- {function} ( ${y} );
  | GetInstance !Wire                                       --  ${x} <- @instance;
  | GetWitness !Wire                                        --  ${x} <- @short_witness;
  | Copy !Wire !Wire                                        --  ${x} <- ${y};
  | Constant !Wire !Value                                   --  ${x} <- < ${c} > ;
  | AssertZero !Wire                                        --  @assert_zero( ${y} );
  | Delete !Wire                                            --  @delete( ${y} );
  | For [IteratorRange] String !Word64 !Word64 LoopAnonCall --  ranges <- @for i @first n1 @last n2 ... @end

data Relation
  = Relation
  { relationHeader :: Header
  , gates :: [Gate]
  }

data Instance
  = Instance
  { instanceHeader :: Header
  , commonInputs :: [Value]
  }

data Witness
  = Witness
  { witnessHeader :: Header
  , shortWitness :: [Value]
  }

data Program
  = Program
  { relation :: Relation
  , witness :: Witness
  , instance_ :: Instance
  }
