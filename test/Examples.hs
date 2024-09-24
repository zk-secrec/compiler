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

module Examples where


import SpecHelper

cubeParams :: Parameters
cubeParams =
  def & witness .~ [r| { "x": "101" } |]
      & instance_ .~ [r| { "z": "1030301" } |]

examples :: Spec
examples =
  describe "examples:" $ do
    it "cube compiles" $
      compilesWith
      cubeParams
      [r|
        fn cube(x : uint $post @prover) -> uint @prover {
            let a = 1;
            let b = a * x;
            let c = b * x;
            let d = c * x;
            d
        }

        fn main() {
            let z = witness { get_instance("z") };
            let x = witness { get_witness("x") };
            let y = cube(x);
            assert (y == z as @prover);
        }
        |]

    it "pow compiles" $
      compilesWith
      cubeParams
      [r|
        fn pow(x : uint $post @prover, n : uint $pre @public) -> uint $post @prover {
            let pow_x_to_n =
                if ((n == 0) as @prover) {
                    1
                } else {
                    let pow_x_to_n_minus_1 = pow(x, n - 1);
                    x * pow_x_to_n_minus_1
                };
            pow_x_to_n
        }

        fn main() {
            let z = witness { get_instance("z") };
            let x = witness { get_witness("x") };
            let y = pow(x, 3);
            assert (y == z as @prover);
        }
        |]

    it "pow with for loop compiles" $
      compilesWith
      cubeParams
      [r|
        fn main() {
            let z = witness { get_instance("z") };
            let x = witness { get_witness("x") };
            let rec xpows : list[uint @prover] =
                for i in 0 .. 4 {
                    if ((i == 0) as @prover) {
                        1
                    } else {
                        x * xpows[i - 1]
                    }
                };
            let y = xpows[3];
            assert (y == z as @prover);
        }
        |]

    it "pow with public exponent list compiles" $
      compilesWith
      cubeParams
      [r|
        fn pow(x : uint $post @prover, n : uint $pre @public) -> uint $post @prover {
            let pow_x_to_n =
                if ((n == 0) as @prover) {
                    1
                } else {
                    let pow_x_to_n_minus_1 = pow(x, n - 1);
                    x * pow_x_to_n_minus_1
                };
            pow_x_to_n
        }

        fn main() {
            let z = witness { get_instance("z") };
            let x = witness { get_witness("x") };
            let arr = [6, 9, 12];
            for i in 2 .. 5 {
                let a = pow(x, arr[i-2]);
                let b = pow(z as @prover, i);
                assert(a == b);
            }
            {}
        }
        |]

    it "sum compiles" $
      compilesWith
      (def & witness .~ [r| { "y": "308" } |]
           & instance_ .~ [r| { "xs": ["11", "22", "33", "44", "55", "66", "77"] } |]
           & public ?~ [r| { "xs": "7" } |])
      [r|
        fn sum(xs : list[uint @verifier]) -> uint @verifier {
            let rec sums = for i in 0 .. length(xs) + 1 {
                if (i == 0) {
                    0
                } else {
                    sums[i - 1] + xs[i - 1]
                }
            };
            sums[length(xs)]
        }

        fn main() {
            let xs_pre = get_instance("xs");
            let xs = witness ([scalar; get_public("xs")]) { xs_pre };
            let y = witness { get_witness("y") };
            let s = sum(xs);
            assert(s as @prover == y);
        }
      |]
