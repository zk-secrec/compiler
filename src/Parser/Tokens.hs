{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Parser.Tokens where

import Parser.HasEOF
import Basic.Location
import qualified Data.Text as Text

data Token
  = TokArr
  | TokArrow
  | TokAs
  | TokAssign
  | TokAt
  | TokBin
  | TokBitwise
  | TokBool
  | TokBreak
  | TokChallenge
  | TokChar Char
  | TokColon
  | TokColonColon
  | TokComma
  | TokContinue
  | TokConvertible
  | TokCurlyHashLeft
  | TokCurlyHashHashLeft
  | TokCurlyLeft
  | TokCurlyRight
  | TokDbgAssert
  | TokDbgAssertEq
  | TokDefault
  | TokDollar
  | TokDomain
  | TokDot
  | TokDotDot
  | TokDotParen
  | TokDoubleArrow
  | TokEff
  | TokElse
  | TokEndStringLiteral
  | TokEOF
  | TokExclam
  | TokExtendedArithmetic
  | TokExtern
  | TokFalse
  | TokField
  | TokFn
  | TokFor
  | TokForAll
  | TokHole
  | TokId Text.Text
  | TokIf
  | TokImpl
  | TokIn
  | TokInf
  | TokInfix
  | TokInfixL
  | TokInfixR
  | TokInt
  | TokInteger Integer
  | TokLet
  | TokList
  | TokLte
  | TokMatch
  | TokMut
  | TokNat
  | TokObliviousChoice
  | TokParenLeft
  | TokParenRight
  | TokPermutationCheck
  | TokPlain
  | TokPlus
  | TokPost
  | TokPostRing
  | TokPostConvertible
  | TokPre
  | TokProver
  | TokPub
  | TokPublic
  | TokQualified
  | TokRec
  | TokRef
  | TokReturn
  | TokRing
  | TokSelfId
  | TokSelfType
  | TokSemiColon
  | TokSieve
  | TokSquareLeft
  | TokSquareRight
  | TokStage
  | TokStar
  | TokStartStringLiteral
  | TokStore
  | TokString
  | TokStruct
  | TokSymbol Text.Text
  | TokTrue
  | TokTrace
  | TokTuple
  | TokType
  | TokUInt
  | TokUnchecked
  | TokUnit
  | TokUnqualified
  | TokUse
  | TokVectors
  | TokVectorization
  | TokVerifier
  | TokWhere
  | TokWhile
  | TokWire
  | TokWith
  | TokWitness
  | TokZip
  deriving (Show, Eq)

instance HasEOF Token where
  mkEOF = TokEOF

  isEOF TokEOF = True
  isEOF _ = False

type LToken = Located Token
