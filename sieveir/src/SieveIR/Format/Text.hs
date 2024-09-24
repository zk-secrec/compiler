{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SieveIR.Format.Text (
  encodeRelation,
  encodeInstance,
  encodeWitness,
  encodeProgram,
  encodePartialProgram
) where

import Data.List (intercalate)
import Data.Word (Word64)
import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ

import SieveIR.Types


nl :: Doc
nl = char '\n'

prettyVersion :: Version -> Doc
prettyVersion (Version major minor patch) =
  "version" <+> int major <> "." <> int minor <> "." <> int patch <> ";"

prettyProfile :: Profile -> Doc
prettyProfile profile =
  "profile" <+> p <> ";"
  where
    p = case profile of
      CircuitArithmeticSimple -> "circ_arithmetic_simple"
      CircuitBooleanSimple -> "circ_boolean_simple"

prettyField :: Field -> Doc
prettyField Field{..} =
  "field" $+$ nest 2
    ("characteristic" <+> text (show characteristic) $+$
     "degree" <+> int degree <> ";")

prettyHeader :: Header -> Doc
prettyHeader Header{..} =
  vcat [ prettyVersion version
       , prettyProfile profile
       , prettyField field <> nl
       ]

prettyBinFun :: BinaryFunction -> Doc
prettyBinFun fun = case fun of
  Mul -> "mul"
  Add -> "add"
  And -> "and"
  Xor -> "xor"

prettyBinCFun :: BinaryConstFunction -> Doc
prettyBinCFun fun = case fun of
  MulC -> "mulc"
  AddC -> "addc"

prettyUnaryFun :: UnaryFunction -> Doc
prettyUnaryFun Not = "not"

wire :: Wire -> Doc
wire w = "$" <> text (show w)

value :: Value -> Doc
value v = "<" <> text (show v) <> ">"

prettyConst :: Wire -> Value -> Doc
prettyConst left right = wire left <+> "<-" <+> value right <> ";"

prettyGate :: Gate -> Doc
prettyGate gate = case gate of
  Binary out fun left right ->
    pretty (wire out) (prettyBinFun fun) (wire left) (wire right)

  BinaryConst out fun left right ->
    pretty (wire out) (prettyBinCFun fun) (wire left) (value right)

  Unary left fun right ->
    wire left <+> "<-" <+> "@" <>
    prettyUnaryFun fun <> parens (wire right) <> ";"

  Copy left right -> wire left <+> "<-" <+> wire right <> ";"

  Constant left right -> prettyConst left right

  AssertZero w -> "assert_zero" <> parens (wire w) <> ";"

  where
    pretty out fun left right =
      out <+> "<-" <+> "@" <> fun <>
      parens (left <> comma <+> right) <> ";"

prettyCount :: Doc -> Word64 -> Doc
prettyCount label count =
  label $+$ nest 2 ("fe:" <+> text (show count) <> ";")

prettyCounts :: Counts -> Doc
prettyCounts Counts{..} =
  vcat [ prettyCount "num_wires" numWires
       , prettyCount "instance" numCommonInputs
       , prettyCount "short_witness" numShortWitness <> nl
       ]

prettyRelation :: Relation -> Doc
prettyRelation Relation{..} =
  vcat
  [ prettyHeader relationHeader
  , prettyCounts relationCounts
  , "relation"
  , nest 2 (vcat $ map prettyGate gates)
  , "end_relation"
  ]

prettyAssignment :: Assignment -> Doc
prettyAssignment (Assignment left right) = prettyConst left right

prettyInputs :: Doc -> Header -> Counts -> [Assignment] -> Doc
prettyInputs tipe header counts assignments =
  vcat
  [ prettyHeader header
  , prettyCounts counts
  , tipe
  , nest 2 (vcat $ map prettyAssignment assignments)
  ]

prettyInstance :: Instance -> Doc
prettyInstance Instance{..} =
  prettyInputs "instance" instanceHeader instanceCounts commonInputs

prettyWitness :: Witness -> Doc
prettyWitness Witness{..} =
  prettyInputs "short_witness" witnessHeader witnessCounts shortWitness

encodeRelation :: Relation -> String
encodeRelation = render . prettyRelation

encodeInstance :: Instance -> String
encodeInstance = render . prettyInstance

encodeWitness :: Witness -> String
encodeWitness = render . prettyWitness

encodeProgram :: Program -> String
encodeProgram Program{..} =
  intercalate "\n\n"
  [ encodeRelation relation
  , encodeInstance instance_
  , encodeWitness witness
  ]

-- Encode for a party (e.g. verifier or TTP) that may not have the instance and/or witness
encodePartialProgram :: Bool -> Bool -> Program -> String
-- encodePartialProgram hasInstance hasWitness prog
encodePartialProgram True True prog = encodeProgram prog
encodePartialProgram True False Program{..} =
  encodeRelation relation ++ "\n\n" ++ encodeInstance instance_
encodePartialProgram False _ Program{..} = encodeRelation relation
