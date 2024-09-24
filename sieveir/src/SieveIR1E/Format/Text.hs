{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SieveIR1E.Format.Text (
  encodeRelation,
  encodeInstance,
  encodeWitness,
  encodeProgram,
  encodePartialProgram,
  encodeGate,
  encodeValue,
  encodeRelationHeader,
  encodeInstanceHeader,
  encodeWitnessHeader,
  encodeFooter
) where

import Data.List (intercalate)
import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ

import SieveIR1E.Types


--nl :: Doc
--nl = char '\n'

prettyVersion :: Version -> Doc
prettyVersion VersionExperimentalFieldSwitching = "version experimental-field-switching;"
--prettyVersion (Version major minor patch) =
--  "version" <+> int major <> "." <> int minor <> "." <> int patch <> ";"

--prettyProfile :: Profile -> Doc
--prettyProfile profile =
--  "gate_set:" <+> p <> ";"
--  where
--    p = case profile of
--      CircuitArithmeticSimple -> "arithmetic"
--      CircuitBooleanSimple -> "boolean"

prettyField :: Field -> Doc
prettyField Field{..} =
  "field" <+> name <+> "characteristic" <+> text (show characteristic) <> ";"

prettyFieldAssertEqual :: FieldAssertEqual -> Doc
prettyFieldAssertEqual (FieldAssertEqual f1 n1 f2 n2) =
  "@assert_equal(" <> name f1 <> ": " <> text (show n1) <> ", " <> name f2 <> ": " <> text (show n2) <> ");"

prettyHeader :: Header -> Doc
prettyHeader Header{..} =
  vcat [ prettyVersion version
       , vcat (map prettyField fields)
       ]

-- an extra part of the header (in addition to prettyHeader) for relation (but not instance/witness) 
prettyExtraHeader :: Header -> Doc
prettyExtraHeader Header{..} =
  vcat (map prettyFieldAssertEqual fieldAssertEquals)

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
value Val{..} = "<" <> name field <> ": " <> text (show val) <> ">"

wireOrConst :: WireOrConst -> Doc
wireOrConst (Left w) = wire w
wireOrConst (Right c) = value c

prettyConst :: Wire -> Value -> Doc
prettyConst left right = wire left <+> "<-" <+> value right <> ";"

prettyValue :: Value -> Doc
prettyValue right = value right <> ";"

prettyIteratorExpr :: IteratorExpr -> Doc
prettyIteratorExpr (IEConst c) = text (show c)
prettyIteratorExpr (IEVar s) = text s
prettyIteratorExpr (IEAdd e1 e2) = "(" <> prettyIteratorExpr e1 <+> "+" <+> prettyIteratorExpr e2 <> ")"
prettyIteratorExpr (IESub e1 e2) = "(" <> prettyIteratorExpr e1 <+> "-" <+> prettyIteratorExpr e2 <> ")"
prettyIteratorExpr (IEMul e1 e2) = "(" <> prettyIteratorExpr e1 <+> "*" <+> prettyIteratorExpr e2 <> ")"

prettyIteratorExpr' :: IteratorExpr -> Doc
prettyIteratorExpr' e = "$" <> prettyIteratorExpr e

prettyIteratorRange :: IteratorRange -> Doc
prettyIteratorRange (IE ie) = prettyIteratorExpr' ie
prettyIteratorRange (IERange ie1 ie2) = prettyIteratorExpr' ie1 <> "..." <> prettyIteratorExpr' ie2

prettyGate :: Gate -> Doc
prettyGate gate = case gate of
  Binary out fun left right ->
    pretty (wire out) (prettyBinFun fun) (wire left) (wire right)

  BinaryConst out fun left right ->
    pretty (wire out) (prettyBinCFun fun) (wire left) (value right)

  Unary left fun right ->
    wire left <+> "<-" <+> "@" <>
    prettyUnaryFun fun <> parens (wire right) <> ";"

  GetInstance left ->
    wire left <+> "<-" <+> "@instance;"

  GetWitness left ->
    wire left <+> "<-" <+> "@short_witness;"

  Copy left right -> wire left <+> "<-" <+> wire right <> ";"

  Constant left right -> prettyConst left right

  AssertZero w -> "@assert_zero" <> parens (wire w) <> ";"

  AssertEqual ws1 ws2 _ _ -> "@assert_equal" <> parens (hsep (punctuate "," (map wire ws1)) <> "; " <> hsep (punctuate "," (map wire ws2))) <> ";"

  AssertEqualConst w c -> "@assert_equal_const" <> parens (wire w <> "; " <> value c) <> ";"

  AssertEqualConst2 ws1 ws2 -> "@assert_equal_const2" <> parens (hsep (punctuate "," (map wireOrConst ws1)) <> "; " <> hsep (punctuate "," (map wireOrConst ws2))) <> ";"

  Delete w -> "@delete" <> parens (wire w) <> ";"

  For ranges x n1 n2 (LoopAnonCall ies1 ies2 numInst numWitn gates) ->
    vcat [(if null ranges then "" else (hsep $ punctuate "," $ map prettyIteratorRange ranges) <+> "<- ") <>
          "@for" <+> text x <+> "@first" <+> text (show n1) <+> "@last" <+> text (show n2),
          nest 2 $ vcat [
            (if null ies1 then "" else (hsep $ punctuate "," $ map prettyIteratorExpr' ies1) <+> "<- ") <>
            "@anon_call(" <> (hsep $ punctuate "," $ map prettyIteratorExpr' ies2 ++
                    ["@instance:" <+> text (show numInst), "@short_witness:" <+> text (show numWitn)]) <> ")",
            nest 2 $ vcat (map prettyGate gates),
            "@end"],
          "@end"]

  where
    pretty out fun left right =
      out <+> "<-" <+> "@" <> fun <>
      parens (left <> comma <+> right) <> ";"

prettyRelation :: Relation -> Doc
prettyRelation Relation{..} =
  vcat
  [ prettyHeader relationHeader
  , "relation"
  , prettyExtraHeader relationHeader
  , "@begin"
  , nest 2 (vcat $ map prettyGate gates)
  , "@end"
  ]

prettyRelationHeader :: Header -> Doc
prettyRelationHeader relationHeader =
  vcat
  [ prettyHeader relationHeader
  , "relation"
  , prettyExtraHeader relationHeader
  , "@begin"
  ]

prettyInputsHeader :: Doc -> Header -> Doc
prettyInputsHeader tipe header =
  vcat
  [ prettyHeader header
  , tipe <+> "@begin"
  ]

prettyInputs :: Doc -> Header -> [Value] -> Doc
prettyInputs tipe header values =
  vcat
  [ prettyHeader header
  , tipe <+> "@begin"
  , nest 2 (vcat $ map prettyValue values)
  , "@end"
  ]

prettyInstance :: Instance -> Doc
prettyInstance Instance{..} =
  prettyInputs "instance" instanceHeader commonInputs

prettyWitness :: Witness -> Doc
prettyWitness Witness{..} =
  prettyInputs "short_witness" witnessHeader shortWitness

encodeGate :: Gate -> String
encodeGate = render . nest 2 . prettyGate

encodeValue :: Value -> String
encodeValue = render . nest 2 . prettyValue

encodeRelationHeader :: Header -> String
encodeRelationHeader = render . prettyRelationHeader

encodeInstanceHeader :: Header -> String
encodeInstanceHeader = render . prettyInputsHeader "instance"

encodeWitnessHeader :: Header -> String
encodeWitnessHeader = render . prettyInputsHeader "short_witness"

encodeFooter :: String
encodeFooter = "@end"

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
