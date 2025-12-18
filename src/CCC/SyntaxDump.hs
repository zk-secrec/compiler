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

module CCC.SyntaxDump where

import Basic.Location
import CCC.Syntax
import Support.Pretty


--
-- Helpers copied from Parser.SyntaxDump
--

ind :: Doc a -> Doc a
ind = indent 2

withName :: String -> Doc ann -> Doc ann
withName name doc = pretty name <> colon $$ ind doc

withNameAndLoc :: String -> Location -> Doc ann -> Doc ann
withNameAndLoc name loc doc =
  pretty name <> colon <+> "//" <+> pretty loc $$ ind doc

withLocationInline :: String -> (a -> Doc ann) -> Located a -> Doc ann
withLocationInline name showInline (Located loc x) =
  pretty name <> colon <+> showInline x <+> "//" <+> pretty loc

withLocation :: String -> (a -> Doc ann) -> Located a -> Doc ann
withLocation name showIndent (Located loc x) =
  pretty name <> colon <+> "//" <+> pretty loc $$ ind (showIndent x)

maybePrint :: (a -> Doc ann) -> Maybe a -> Doc ann
maybePrint = maybe emptyDoc

dumpList :: (a -> Doc ann) -> [a] -> Doc ann
dumpList f = vcat . map f


--
-- Syntax dumping
--

dumpCCCPlugin
  :: (Pretty name)
  => CCCPlugin name -> Doc ann
dumpCCCPlugin (CCCPlugin lversioned)
  = withLocationInline "Plugin" pretty lversioned

dumpCCCPred
  :: CCCPred -> Doc ann
dumpCCCPred (CCCLT ln)
  = withLocationInline "LessThan" pretty ln
dumpCCCPred (CCCGT ln)
  = withLocationInline "GreaterThan" pretty ln
dumpCCCPred (CCCEQ ln)
  = withLocationInline "Equals" pretty ln
dumpCCCPred CCCMersenne
  = "IsMersenne"
dumpCCCPred CCCProth
  = "IsProth"
dumpCCCPred CCCPow2
  = "IsPowerOf2"

dumpCCCType
  :: Pretty name
  => CCCType name -> Doc ann
dumpCCCType t@ (CCCField _)
  = withName "Field" $
      withName "fieldPreds" (dumpList (withLocation "fieldPred" dumpCCCPred) (_cccFieldPreds t))
dumpCCCType t@ (CCCExtField _ _ _)
  = withName "ExtField" $
      withName "baseFields" (dumpList (withLocation "baseField" pretty) (_cccBaseFields t)) $$
      withName "degPreds" (dumpList (withLocation "degPred" dumpCCCPred) (_cccDegPreds t)) $$
      withName "polPreds" (dumpList (withLocation "polPred" dumpCCCPred) (_cccPolPreds t))
dumpCCCType t@ (CCCRing _)
  = withName "Ring" $
      withName "widthPreds" (dumpList (withLocation "widthPred" dumpCCCPred) (_cccWidthPreds t))
dumpCCCType t@ (CCCBitwise _)
  = withName "Bitwise" $
      withName "bitwisePreds" (dumpList (withLocation "bitwisePred" dumpCCCPred) (_cccBitwisePreds t))
dumpCCCType    (CCCPluginType name)
  = withLocationInline "PluginType" pretty name

dumpCCCChallenge
  :: CCCChallenge -> Doc ann
dumpCCCChallenge (CCCChallenge lix)
  = withName "Challenge" $
      withLocationInline "type" pretty lix

dumpCCCConversion
  :: CCCConversion -> Doc ann
dumpCCCConversion (CCCConversion loix liix)
  = withName "Conversion" $
      withLocationInline "out" pretty loix $$
      withLocationInline "in" pretty liix

dumpCCCConstraintArg
  :: (Pretty name)
  => CCCConstraintArg name -> Doc ann
dumpCCCConstraintArg (CCCNameArg lname)
  = withLocationInline "Name" pretty lname
dumpCCCConstraintArg (CCCPredArg lpred)
  = withLocationInline "Pred" dumpCCCPred lpred
dumpCCCConstraintArg (CCCNumArg ln)
  = withLocationInline "Num" pretty ln

dumpCCCConstraint
  :: (Pretty name)
  => CCCConstraint name -> Doc ann
dumpCCCConstraint (CCCConstraint args)
  = withName "Constraint" $
      withName "constraintArgs" (dumpList (withLocation "constraintArg" dumpCCCConstraintArg) args)

dumpCCCConstraintBlock
  :: (Pretty name)
  => CCCConstraintBlock name -> Doc ann
dumpCCCConstraintBlock (CCCConstraintBlock lname cs)
  = withName "ConstraintBlock" $
      withLocationInline "plugin" pretty lname $$
      withName "constraints" (dumpList (withLocation "constraint" dumpCCCConstraint) cs)

dumpCCC
  :: (Pretty name)
  => CCC name -> Doc ann
dumpCCC ccc
  = withName "CCC" $
      withLocationInline "version" pretty (_cccVersion ccc) $$
      withName "plugins" (dumpList (withLocation "plugin" dumpCCCPlugin) (_cccPlugins ccc)) $$
      withName "types" (dumpList (withLocation "type" dumpCCCType) (_cccTypes ccc)) $$
      withName "challenges" (dumpList (withLocation "challenge" dumpCCCChallenge) (_cccChallenges ccc)) $$
      withName "conversions" (dumpList (withLocation "conversion" dumpCCCConversion) (_cccConversions ccc)) $$
      withName "constraints" (dumpList (withLocation "constratintBlock" dumpCCCConstraintBlock) (_cccConstraints ccc))

