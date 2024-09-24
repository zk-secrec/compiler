{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SieveIR.Format.Binary (
  encodeInstance,
  encodeWitness,
  encodeRelation,
  encodeProgram,
  instanceBuilder,
  witnessBuilder,
  relationBuilder,
  programBuilder
) where

import Control.Monad.State.Strict (modify', execState, gets)
import Data.Binary.Put (runPut)
import Data.Bits (shiftR)
import Data.List (unfoldr)
import Data.Monoid (Sum(..))
import Data.Semigroup (Max(..))
import Data.Word (Word8)
import FlatBuffers.Internal.Constants (uoffsetSize)
import FlatBuffers.Internal.Write (FBState(..), WriteTable(..), alignTo, uoffsetFrom, writeInt32)
import Numeric.Natural

import qualified Data.Binary as Binary
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString.Lazy as BS
import qualified Data.Text as T
import qualified FlatBuffers as FB
import qualified FlatBuffers.Vector as Vector
import qualified SieveIR.Internal.Schema as Schema

import SieveIR.Types


writeValue :: Value -> Vector.WriteVector Word8
writeValue val = Vector.fromList len bytes
  where
    bytes = BS.unpack $ writeNatural val
    len = fromIntegral $ length bytes

writeNatural :: Natural -> BS.ByteString
writeNatural 0 = runPut $ Binary.putWord8 0
writeNatural i = runPut $ mapM_ Binary.putWord8 $ unroll i

unroll :: Natural -> [Word8]
unroll i = unfoldr step i
  where
    step 0 = Nothing
    step i = Just (fromIntegral i, i `shiftR` 8)

tshow :: Show a => a -> T.Text
tshow = T.pack . show

writeHeader :: Header -> WriteTable Schema.Header
writeHeader header =
  Schema.header
  (Just version')
  (Just profile')
  (Just characteristic')
  (Just degree')
  where
    Version major minor patch = version header
    version' = mconcat [tshow major, ".", tshow minor, ".", tshow patch]
    characteristic' = writeValue $ characteristic $ field header
    degree' = fromIntegral $ degree $ field header
    profile' = case profile header of
      CircuitArithmeticSimple -> "circ_arithmetic_simple"
      CircuitBooleanSimple -> "circ_boolean_simple"

writeWire :: Wire -> Maybe (FB.WriteStruct Schema.Wire)
writeWire = Just . Schema.wire

writeBinaryGate :: Wire -> BinaryFunction -> Wire -> Wire -> FB.WriteUnion Schema.GateSet
writeBinaryGate out fun left right = case fun of
  Add -> Schema.gateSetGateAdd $ Schema.gateAdd out' left' right'
  Mul -> Schema.gateSetGateMul $ Schema.gateMul out' left' right'
  And -> Schema.gateSetGateAnd $ Schema.gateAnd out' left' right'
  Xor -> Schema.gateSetGateXor $ Schema.gateXor out' left' right'
  where
    out' = writeWire out
    left' = writeWire left
    right' = writeWire right

writeBinaryConstGate :: Wire -> BinaryConstFunction -> Wire -> Value ->
  FB.WriteUnion Schema.GateSet
writeBinaryConstGate out fun left right = case fun of
  AddC -> Schema.gateSetGateAddConstant $ Schema.gateAddConstant out' left' right'
  MulC -> Schema.gateSetGateMulConstant $ Schema.gateMulConstant out' left' right'
  where
    out' = writeWire out
    left' = writeWire left
    right' = Just $ writeValue right

writeGate :: Gate -> WriteTable Schema.Gate
writeGate gate = case gate of
  Binary out fun left right ->
    Schema.gate $ writeBinaryGate out fun left right
  BinaryConst out fun left right ->
    Schema.gate $ writeBinaryConstGate out fun left right
  Unary output Not input ->
    Schema.gate $
    Schema.gateSetGateNot $
    Schema.gateNot (writeWire output) (writeWire input)
  Copy output input ->
    Schema.gate $
    Schema.gateSetGateCopy $
    Schema.gateCopy (writeWire output) (writeWire input)
  Constant output input ->
    Schema.gate $
    Schema.gateSetGateConstant $
    Schema.gateConstant (writeWire output) (Just $ writeValue input)
  AssertZero input ->
    Schema.gate $
    Schema.gateSetGateAssertZero $
    Schema.gateAssertZero (writeWire input)

writeRelation :: Relation -> WriteTable Schema.Root
writeRelation Relation{..} =
  Schema.root $
  Schema.messageRelation $
  Schema.relation
  (Just $ writeHeader relationHeader)
  (Just 0)
  (Just 0)
  (Just 0)
  gates'
  where
    gateWriters = map writeGate gates
    len = fromIntegral $ length gateWriters
    gates' = Just $ Vector.fromList len gateWriters

writeAssignment :: Assignment -> WriteTable Schema.Assignment
writeAssignment (Assignment wire value) =
  Schema.assignment (writeWire wire) (Just $ writeValue value)

writeInstance :: Instance -> WriteTable Schema.Root
writeInstance Instance{..} =
  Schema.root $
  Schema.messageInstance $
  Schema.instance_ (Just $ writeHeader instanceHeader) inputs
  where
    inputWriters = map writeAssignment commonInputs
    len = fromIntegral $ length inputWriters
    inputs = Just $ Vector.fromList len inputWriters

writeWitness :: Witness -> WriteTable Schema.Root
writeWitness Witness{..} =
  Schema.root $
  Schema.messageWitness $
  Schema.witness (Just $ writeHeader witnessHeader) assignments
  where
    writers = map writeAssignment shortWitness
    len = fromIntegral $ length writers
    assignments = Just $ Vector.fromList len writers

encode :: WriteTable a -> Builder.Builder
encode = encodeState (FBState mempty (Sum 0) (Max 1) mempty)

{-# INLINE encodeState #-}
encodeState :: FBState -> WriteTable a -> Builder.Builder
encodeState state (WriteTable writeTable) =
  builder $
  execState
    (do pos <- writeTable
        maxAlignment <- gets (getMax . maxAlign)
        modify' $ alignTo maxAlignment (uoffsetSize + uoffsetSize)
        modify' $ uoffsetFrom pos
        size <- gets (getSum . bufferSize)
        modify' $ writeInt32 size
    )
    state

encodeInstance :: Instance -> BS.ByteString
encodeInstance = Builder.toLazyByteString . instanceBuilder

encodeWitness :: Witness -> BS.ByteString
encodeWitness = Builder.toLazyByteString . witnessBuilder

encodeRelation :: Relation -> BS.ByteString
encodeRelation = Builder.toLazyByteString . relationBuilder

encodeProgram :: Program -> BS.ByteString
encodeProgram = Builder.toLazyByteString . programBuilder

instanceBuilder :: Instance -> Builder.Builder
instanceBuilder = encode . writeInstance

witnessBuilder :: Witness -> Builder.Builder
witnessBuilder = encode . writeWitness

relationBuilder :: Relation -> Builder.Builder
relationBuilder = encode . writeRelation

programBuilder :: Program -> Builder.Builder
programBuilder Program{..} =
  instanceBuilder instance_ <>
  witnessBuilder witness <>
  relationBuilder relation
