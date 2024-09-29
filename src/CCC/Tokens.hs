{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module CCC.Tokens where

import Parser.HasEOF
import Basic.Location
import qualified Data.Text as Text

data Token
  = TokVersion
  | TokConfiguration
  | TokChallenge
  | TokPlugin
  | TokType
  | TokField
  | TokExtField
  | TokRing
  | TokConvert
  | TokOut
  | TokIn
  | TokConstraints
  | TokConstraint
  | TokLessThan
  | TokGreaterThan
  | TokEquals
  | TokMersenne
  | TokProth
  | TokPow2
  | TokBegin
  | TokEnd
  | TokParenLeft
  | TokParenRight
  | TokDot
  | TokComma
  | TokColon
  | TokSemicolon
  | TokInt Integer
  | TokId Text.Text
  | TokEOF
  deriving (Show, Eq)

instance HasEOF Token where
  mkEOF = TokEOF

  isEOF TokEOF = True
  isEOF _ = False

type LToken = Located Token
