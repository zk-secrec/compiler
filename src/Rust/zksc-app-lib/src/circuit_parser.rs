/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use std::cell::RefCell;
use std::str::FromStr;

use crate::value::*;

#[derive(Debug)]
pub enum Gate {
    And(usize, usize, usize),
    Xor(usize, usize, usize),
    Not(usize, usize),
    CopyWire(usize, usize),
}
use Gate::*;

#[derive(Debug)]
pub struct Circuit {
    pub num_wires: usize,
    pub input_wires: Vec<Vec<usize>>,
    pub output_wires: Vec<Vec<usize>>,
    pub gates: Vec<Gate>,
}

fn vec_from(start: usize, count: usize) -> Vec<usize> {
    (start..start + count).collect()
}

fn vecvec_from(start: usize, counts: Vec<usize>) -> Vec<Vec<usize>> {
    let mut v = Vec::new();
    let mut next = start;
    for count in counts {
        v.push(vec_from(next, count));
        next += count;
    }
    v
}

pub fn eval_circuit(c: &Circuit, inputs: Vec<Vec<bool>>) -> Vec<Vec<bool>> {
    let mut arr = Vec::new();
    arr.resize(c.num_wires, false);
    assert!(
        c.input_wires.len() == inputs.len(),
        "Invalid number of inputs to circuit call"
    );
    for i in 0..inputs.len() {
        assert!(
            c.input_wires[i].len() == inputs[i].len(),
            "Invalid length of an input in circuit call"
        );
        for j in 0..inputs[i].len() {
            arr[c.input_wires[i][j]] = inputs[i][j];
        }
    }
    for g in &c.gates {
        match g {
            And(x, y, z) => {
                arr[*x] = arr[*y] && arr[*z];
            }
            Xor(x, y, z) => {
                arr[*x] = arr[*y] ^ arr[*z];
            }
            Not(x, y) => {
                arr[*x] = !arr[*y];
            }
            CopyWire(x, y) => {
                arr[*x] = arr[*y];
            }
        }
    }
    let mut outputs = Vec::new();
    for i in 0..c.output_wires.len() {
        let mut output = Vec::new();
        for j in 0..c.output_wires[i].len() {
            output.push(arr[c.output_wires[i][j]]);
        }
        outputs.push(output);
    }
    outputs
}

pub fn get_unknown_outputs_for_circuit(c: &Circuit) -> Vec<Vec<Value>> {
    let unknown = rep::Unknown::new(rep::PartOfUnknown::new());
    let mut outputs = Vec::new();
    for i in 0..c.output_wires.len() {
        let mut output = Vec::new();
        for _ in 0..c.output_wires[i].len() {
            output.push(unknown.clone());
        }
        outputs.push(output);
    }
    outputs
}

pub fn parse_circuit_from_str(s: &str) -> Circuit {
    let mut words = Vec::new();
    let mut curr_word = String::new();
    for c in s.chars() {
        if c.is_ascii_whitespace() {
            if !curr_word.is_empty() {
                words.push(curr_word.clone());
            }
            curr_word.clear();
        } else {
            curr_word.push(c);
        }
    }
    // handle missing EOL at EOF
    if !curr_word.is_empty() {
        words.push(curr_word);
    }
    // Cannot get the borrowing rules satisfied with let mut, so have to use RefCell instead, which has fewer restrictions
    //let mut next_index = 0;
    let next_index = RefCell::new(0);
    let next_word = || {
        let s = &words[*next_index.borrow()];
        *next_index.borrow_mut() += 1;
        s
    };
    let next_int = || usize::from_str(next_word()).expect("Failed to parse integer");
    let next_vec = |n| {
        let mut v = Vec::new();
        for _ in 0..n {
            v.push(next_int());
        }
        v
    };
    let num_gates = next_int();
    let num_wires = next_int();
    let num_inputs = next_int();
    let input_lengths = next_vec(num_inputs);
    let num_outputs = next_int();
    let output_lengths = next_vec(num_outputs);
    let mut gates = Vec::new();
    for _ in 0..num_gates {
        let num_inps = next_int();
        let num_outps = next_int();
        let inps = next_vec(num_inps);
        let outps = next_vec(num_outps);
        let oper = next_word();
        let g = match &oper[..] {
            "AND" => And(outps[0], inps[0], inps[1]),
            "XOR" => Xor(outps[0], inps[0], inps[1]),
            "INV" => Not(outps[0], inps[0]),
            "EQW" => CopyWire(outps[0], inps[0]),
            _ => panic!("Unsupported gate type: {}", oper),
        };
        gates.push(g);
    }
    let output_start = num_wires - output_lengths.iter().sum::<usize>();
    let circuit = Circuit {
        num_wires: num_wires,
        input_wires: vecvec_from(0, input_lengths),
        output_wires: vecvec_from(output_start, output_lengths),
        gates: gates,
    };

    circuit
}
