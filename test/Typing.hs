{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

{-
 - Copyright 2024 Cybernetica AS
 - 
 - Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 - 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 - 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 - 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 - THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 -}

module Typing where

import Basic.Location (unLocated)
import Basic.Name (nameOccName)
import Basic.Var (idType, varName)
import Data.Maybe (fromJust)
import Parser.Syntax
import SpecHelper
import Typing.Typing


typing :: Spec
typing =
  describe "typing:" $ do
    it "can't assign @d1 to @d2 if @d1 < @d2" $
      compileFails
      [r|
        fn main() {
          let x: uint $pre @prover = 1;
          let y: uint $pre @public = x;
        }
      |]
      "inline:4:38:\n *Unsolved constraints: @public ~ @prover"

    it "main has type () -> ()" $ do
      program <- typeCheck "fn main() {}"
      let TForAll _ _ mainTy = idType $ _tFunName $
            fromJust $ findFunction "main" program
      mainTy `typeShouldBe` mkFunArgs [mkTypeUnit] mkTypeUnit

    it "can infer stage-polymorphic function type" $
      compiles
      [r|
        fn f() -> bool {
          let x: bool = true;
          x
        }

        fn main() {
          let x: bool $pre = f();
          let y: bool $post = f();
        }
      |]

    it "can't unify $pre with $post" $
      compileFails
      [r|
        fn main() {
          let x: uint $pre @prover = 1;
          let y: uint $post @prover = x;
        }
      |]
      "inline:4:39:\n *Unsolved constraints: \\$post ~ \\$pre"

    it "report error when stage can't be inferred" $
      compileFails
      [r|
        fn main() {
          let x: uint @prover = 1;
        }
      |]
      "inline:3:\\(18,30\\):\n *Failed to infer stage."

    it "witness expression converts $pre to $post" $
      compiles
      [r|
        fn main() {
          let x: uint $pre @prover = 1;
          let y: uint $post @prover = witness { x };
        }
      |]

    it "witness expression unifies stages" $ do
      program <- typeCheck
        [r|
          fn main() {
            let x: uint @prover = 1;
            let y = witness { x };
          }
        |]
      let body = _tFunBody $ fromJust (findFunction "main" program)
          statements = concat [ stmts | Block stmts _ <- universe body ]
          typeOf var =
            let [TForAll _ _ ty] =
                  [ idType (unLocated (_bindName binding))
                  | Let _ binding _ <- statements
                  , nameOccName (varName (unLocated (_bindName binding))) == var
                  ]
            in ty
          xType = typeOf "x"
          yType = typeOf "y"
      xType `typeShouldBe` mkTypeUInt mkPre mkProverDomain
      yType `typeShouldBe` mkTypeUInt mkPost mkProverDomain

    it "witness expression converts tuple component stages" $
      compiles
      [r| fn main() {
            let x: tuple[uint $pre @prover] $pre @prover = (1,);
            let y = witness ((scalar,)) { x };
      }|]

    it "witness expression converts list element stage" $
      compiles
      [r| fn main() {
            let x: list[uint $pre @prover] $pre @prover = [];
            let y: list[uint $post @prover] $pre @prover =
                witness ([scalar; 0]) { x };
      }|]

    it "witness expression converts list domain" $
      compiles
      [r| fn main() {
            let x: list[uint $pre @prover] $pre @prover = [];
            let y: list[uint $post @prover] $pre @public =
              witness ([scalar; 0]) { x };
      }|]

    it "witness expression can't convert tuple domain" $
      compileFails
      [r| fn main() {
            let x: tuple[uint $pre @prover] $pre @prover = (1,);
            let y: tuple[uint $post @prover] $pre @public =
              witness ((scalar,)) { x };
      }|]
      "inline:4:37:\n *Unsolved constraints: @public ~ @prover"
