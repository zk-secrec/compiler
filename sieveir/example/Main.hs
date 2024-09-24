{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.ByteString.Lazy as BS

import SieveIR
import SieveIR.Format.Binary


modulus :: Value
modulus = 101

exampleCounts :: Counts
exampleCounts
  = Counts
  { numWires = 8
  , numCommonInputs = 1
  , numShortWitness = 2
  }

exampleHeader :: Header
exampleHeader
  = Header
  { version = Version 0 0 1
  , profile = CircuitArithmeticSimple
  , field = Field { characteristic = modulus
                  , degree = 1
                  }
  }

exampleRelation :: Relation
exampleRelation
  = Relation
  { relationHeader = exampleHeader
  , relationCounts = exampleCounts
  , gates = [ Constant 3 (modulus - 1)
            , Binary 4 Mul 1 1
            , Binary 5 Mul 2 2
            , Binary 6 Add 4 5
            , Binary 7 Mul 0 3
            , Binary 8 Add 6 7
            , AssertZero 8
            ]
  }

exampleInstance :: Instance
exampleInstance
  = Instance
  { instanceHeader = exampleHeader
  , instanceCounts = exampleCounts
  , commonInputs = [ Assignment 0 25 ]
  }

exampleWitness :: Witness
exampleWitness
  = Witness
  { witnessHeader = exampleHeader
  , witnessCounts = exampleCounts
  , shortWitness = [ Assignment 1 3
                   , Assignment 2 4
                   ]
  }

exampleProgram :: Program
exampleProgram
  = Program
  { instance_ = exampleInstance
  , witness = exampleWitness
  , relation = exampleRelation
  }

main :: IO ()
main = do
  args <- getArgs

  unless (length args == 1) $ do
    putStrLn "Expecting one argument: output filename"
    exitFailure

  let path = head args

  BS.writeFile path $ encodeProgram exampleProgram

  putStrLn $ "Output saved to " ++ path
