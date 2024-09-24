/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use simple_logger::SimpleLogger;
use zksc_app_lib::oob_challenge::OobChallengeBackend;

use std::io::BufWriter;
use std::rc::Rc;
use std::{cell::RefCell, io};
use std::collections::VecDeque;
use std::any::Any;

use zksc_app_lib::command_line::*;
use zksc_app_lib::sieve::challenge_backend;
use zksc_app_lib::*;

use num_bigint::BigInt;
use num_traits::{Zero,One,ToPrimitive};

// if true, write debugging output about function definitions and applications
const DEBUG: bool = false;

fn main() -> Result<()> {
    SimpleLogger::new().init().unwrap();
    let cmdargs = match parse_command_line_args() {
        Err(err) => panic!("{}", err.to_string()),
        Ok(cmdargs) => cmdargs,
    };
    let CommandLineArgs {
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
        output_prefix,
    } = cmdargs;
    let input_public = input_public.as_ref().map(String::as_str);
    let input_instance = input_instance.as_ref().map(String::as_str);
    let input_witness = input_witness.as_ref().map(String::as_str);
    let output = Rc::new(RefCell::new(BufWriter::new(io::stdout())));
    // The order of operations here is important, it must be
    //   1. EmpChallengeBackend::new
    //   2. set_boxed_challenge_backend
    //   3. FilesIR1E::new
    //   4. read_emp_line_1
    // Otherwise it can get into deadlock if challenges with EMP (--interactive) are used.
    let challenge_backend0 = OobChallengeBackend::new(Rc::clone(&output), &output_prefix);
    set_boxed_challenge_backend(Box::new(challenge_backend0));
    let sieve: Box<dyn SIEVEIR> = Box::new(DummyBackend::new());
    challenge_backend().read_emp_line_1();
    set_boxed_sieve_backend(sieve);
    zksc_run(
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
    )
}

#[derive(Debug, Clone)]
struct DummyWire {
    m: BigInt,
    v: BigInt,
}

impl WireTrait for DummyWire {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl Drop for DummyWire {
    fn drop(&mut self) {
        //println!("DummyWire::drop");
    }
}

impl DummyWire {
    fn new(m: BigInt, v: BigInt) -> DummyWire {
        DummyWire { m, v }
    }
}

#[derive(Debug, Clone)]
struct DummyWireRange {
    m: BigInt,
    v: Vec<BigInt>,
}

impl DummyWireRange {
    fn new(m: BigInt, v: Vec<BigInt>) -> DummyWireRange {
        DummyWireRange { m, v }
    }

    fn index(&self, i: usize) -> DummyWire {
        assert!(i < self.v.len());
        DummyWire {
            m: self.m.clone(),
            v: self.v[i].clone(),
        }
    }
}

impl WireRangeTrait for DummyWireRange {
    fn length(&self) -> usize {
        self.v.len()
    }

    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl Drop for DummyWireRange {
    fn drop(&mut self) {
        //println!("DummyWireRange::drop");
    }
}

fn downcast_wire(w: &Wire) -> &DummyWire {
    w.downcast::<DummyWire>()
}

fn downcast_wires<'a>(wires: Vec<&'a Wire>) -> Vec<&'a DummyWire> {
    wires.into_iter().map(|w| downcast_wire(w)).collect()
}

fn downcast_wr(wr: &WireRange) -> &DummyWireRange {
    wr.downcast::<DummyWireRange>()
}

fn downcast_wrs<'a>(wrs: Vec<&'a WireRange>) -> Vec<&'a DummyWireRange> {
    wrs.into_iter().map(|wr| downcast_wr(wr)).collect()
}

fn create_wire(m: &BigInt, v: &BigInt) -> Wire {
    upcast_wire(DummyWire { m: m.clone(), v: v.clone() })
}

fn view_wire(w : &Wire) -> (&BigInt, &BigInt) {
    let w = downcast_wire(w);
    (&w.m, &w.v)
}

fn create_wr(m: BigInt, v: Vec<BigInt>) -> WireRange {
    WireRange::new(DummyWireRange{m, v})
}

fn create_wr_from_wires(m: BigInt, wires: Vec<Wire>) -> WireRange {
    let mut v: Vec<BigInt> = Vec::with_capacity(wires.len());
    for w in wires {
        let (m2, v2) = view_wire(&w);
        assert_eq!(&m, m2, "Values on a wire range do not have the same modulus");
        v.push(v2.clone());
    }
    create_wr(m, v)
}

fn view_wr(wr: &WireRange) -> (&BigInt, &Vec<BigInt>) {
    let wr = downcast_wr(wr);
    (&wr.m, &wr.v)
}

fn get_mod(m: &NatType) -> BigInt {
    m.modulus.clone().expect("infinite modulus in wire")
}

fn assert_moduli_eq(s: &str, _m: &NatType, m1: &BigInt, m2: &BigInt) {
    assert_eq!{m1,m2,"{} called between wires of different types",s};
    assert_eq!{get_mod(_m),*m1,"Wrong modulus provided to {} call",s};
}

fn assert_moduli_eq_2(s: &str, m: &BigInt, m1: &BigInt) {
    assert_eq!{*m, *m1,"Wrong modulus provided when {}", s};
}

fn assert_output_modulus(s: &str, _m: &NatType, m1: &BigInt) {
    assert_eq!{get_mod(_m),*m1,"Wrong modulus provided to {} call",s};
}

fn assert_boolean(m1: &BigInt) {
    assert!(m1.is_one() || m1.is_zero(),"Argument is not boolean");
}

fn assert_underlying_modulus(m: &NatType,w: &Wire) {
    let v = view_wire(w);
    assert_eq!(&v.0,&m.modulus.as_ref().unwrap(),"input modulus is not the same as internal representation");
}

fn new_variable(_m: &NatType, v: &Value) -> Wire {
    match v.view() {
        ValueView::Unknown(_) => create_wire(&get_mod(_m),&Integer::zero()),
        ValueView::ZkscDefined() => {
            let val_bigint = (_m.to_bigint)(v);
            let modulus = &get_mod(_m);
            create_wire(modulus, &(val_bigint % modulus))
        },
        ValueView::Bool(b) => create_wire(&get_mod(_m),&if *b {Integer::one()} else {Integer::zero()}),
        _ => panic!("Unknown value to add as wire: {:?}",v)
    }
}

// Wires used inside function definitions, where the value is not known and an uid is used instead
#[derive(Debug, Clone)]
struct FunWire {
    m: BigInt,
    uid: usize,
}

impl WireTrait for FunWire {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

fn downcast_fun_wire(w: &Wire) -> &FunWire {
    w.downcast::<FunWire>()
}

#[derive(Debug)]
enum FunWireOrConst {
    W(FunWire),
    C(DummyWire),
}

// SIEVEIR trait calls made inside a function definition
#[derive(Debug)]
enum TraitCall {
    // the first FunWire is the destination wire
    Mul(FunWire, NatType, FunWire, FunWire),
    Add(FunWire, NatType, FunWire, FunWire),
    MulC(FunWire, NatType, FunWire, Integer),
    AddC(FunWire, NatType, FunWire, Integer),
    And(FunWire, NatType, FunWire, FunWire),
    Xor(FunWire, NatType, FunWire, FunWire),
    Not(FunWire, NatType, FunWire),
    AssertZero(NatType, FunWire),
    Bool2Int(FunWire, NatType, FunWire, NatType),
    IntFieldSwitch(FunWire, NatType, FunWire, NatType),
    GetInstance(FunWire, NatType),
    GetWitness(FunWire, NatType),
    ZeroWire(FunWire, NatType),
    ConstBool(FunWire, NatType, bool),
    ConstUint(FunWire, NatType, Value),
}

use TraitCall::*;

struct Function {
    num_wires: usize, // total number of wires used by the function (with uids 0, ..., num_wires-1)
    input_moduli: Vec<BigInt>,
    output_moduli: Vec<BigInt>,
    trait_calls: Vec<TraitCall>,
    result: Vec<FunWireOrConst>,
    witness_count: u64,
}

const QUEUE_CAPACITY : usize = 200;

pub struct DummyBackend {
    is_inside_fn_def: RefCell<bool>,
    fun_wire_count: RefCell<usize>, // number of wires used so far in the current function definition
    fun_trait_calls: RefCell<Vec<TraitCall>>, // SIEVEIR trait calls made inside the current function definition
    fun_output_moduli: RefCell<Vec<BigInt>>,
    fun_input_moduli: RefCell<Vec<BigInt>>,
    defined_funs: RefCell<Vec<Function>>,
    instance_queue: RefCell<VecDeque<(NatType, Value)>>,
    witness_queue: RefCell<VecDeque<(NatType, Value)>>
}

impl DummyBackend {
    pub fn new() -> DummyBackend {
        let is_inside_fn_def = RefCell::new(false);
        let fun_wire_count = RefCell::new(0);
        let fun_trait_calls = RefCell::new(Vec::new());
        let fun_output_moduli = RefCell::new(Vec::new());
        let fun_input_moduli = RefCell::new(Vec::new());
        let defined_funs = RefCell::new(Vec::new());
        let instance_queue = RefCell::new(VecDeque::with_capacity(QUEUE_CAPACITY));
        let witness_queue = RefCell::new(VecDeque::with_capacity(QUEUE_CAPACITY));
        DummyBackend {
            is_inside_fn_def,
            fun_wire_count,
            fun_trait_calls,
            fun_output_moduli,
            fun_input_moduli,
            defined_funs,
            instance_queue,
            witness_queue,
        }
    }

    fn inside_fn_def(&self) -> bool {
        *self.is_inside_fn_def.borrow()
    }

    fn assert_outside_fn_def(&self) {
        assert!(!self.inside_fn_def(), "Calling a SIEVEIR trait method that is not allowed inside a function definition");
    }

    fn begin_function_def(&self, mut output_moduli: Vec<BigInt>, mut input_moduli: Vec<BigInt>) -> usize {
        self.assert_outside_fn_def();
        assert!(*self.fun_wire_count.borrow() == 0);
        assert!(self.fun_trait_calls.borrow().is_empty());
        assert!(self.fun_output_moduli.borrow().is_empty());
        assert!(self.fun_input_moduli.borrow().is_empty());
        self.fun_output_moduli.borrow_mut().append(&mut output_moduli);
        self.fun_input_moduli.borrow_mut().append(&mut input_moduli);
        *self.is_inside_fn_def.borrow_mut() = true;
        self.defined_funs.borrow().len()
    }

    fn end_function_def(&self, wires_res: Vec<WireOrConst>) {
        assert!(self.inside_fn_def());
        let mut trait_calls = Vec::new();
        trait_calls.append(&mut self.fun_trait_calls.borrow_mut());
        assert!(self.fun_trait_calls.borrow().is_empty());
        let mut input_moduli = Vec::new();
        input_moduli.append(&mut self.fun_input_moduli.borrow_mut());
        assert!(self.fun_input_moduli.borrow().is_empty());

        let mut output_moduli = Vec::new();
        output_moduli.append(&mut self.fun_output_moduli.borrow_mut());
        assert!(self.fun_output_moduli.borrow().is_empty());
        let result: Vec<FunWireOrConst> = output_moduli.iter().zip(wires_res.into_iter()).map(|(m, woc)| {
            match woc {
                WireOrConst::W(w) => {
                    let w = downcast_fun_wire(w).clone();
                    assert_moduli_eq_2("returning a value from a function", m, &w.m);
                    FunWireOrConst::W(w)
                }
                WireOrConst::C(c) => FunWireOrConst::C(DummyWire { m: m.clone(), v: c }),
            }
        }).collect();
        let num_wires = *self.fun_wire_count.borrow();

        if DEBUG {
            println!("Function definition (uid = {}):", self.defined_funs.borrow().len());
            println!("num_wires: {}", num_wires);
            for m in &input_moduli {
                println!("input, modulus {:?}", m);
            }
            for tc in &trait_calls {
                println!("{:?}", tc);
            }
            for fwoc in &result {
                println!("return {:?}", fwoc);
            }
            for m in &output_moduli {
                println!("output, modulus {:?}", m);
            }
            println!();
        }

        let mut witness_count = 0;
        for tc in &trait_calls {
            match tc {
                GetWitness(_, _) => {
                    witness_count += 1;
                }
                _ => {}
            }
        }

        self.defined_funs.borrow_mut().push(Function {
            num_wires,
            input_moduli,
            output_moduli,
            trait_calls,
            result,
            witness_count,
        });

        *self.is_inside_fn_def.borrow_mut() = false;
        *self.fun_wire_count.borrow_mut() = 0;
    }

    fn add_trait_call(&self, tc: TraitCall) {
        self.fun_trait_calls.borrow_mut().push(tc);
    }

    fn new_fun_wire(&self, m: &NatType) -> FunWire {
        let w = *self.fun_wire_count.borrow();
        *self.fun_wire_count.borrow_mut() = w + 1;
        FunWire { m: get_mod(m), uid: w }
    }

    fn apply_fn(&self, fun: &Function, input_wires: Vec<&DummyWire>) -> Vec<DummyWire> {
        let wires: RefCell<Vec<Option<DummyWire>>> = RefCell::new(Vec::new());
        wires.borrow_mut().resize(fun.num_wires, None);
        for i in 0 .. input_wires.len() {
            let w = input_wires[i].clone();
            assert_moduli_eq_2("giving an argument to a function", &fun.input_moduli[i], &w.m);
            if DEBUG {
                println!("input wire {} := {}, modulus {}", i, &w.v, &w.m);
            }
            wires.borrow_mut()[i] = Some(w);
        }
        let read_wire = |fw: &FunWire| -> Wire {
            match &wires.borrow()[fw.uid] {
                None => panic!("Attempting to use an undefined wire inside a function"),
                Some(dw) => upcast_wire(dw.clone()),
            }
        };
        let assign_wire = |r: &FunWire, w: Wire| {
            match &wires.borrow()[r.uid] {
                None => {}
                Some(_) => panic!("Reassigning a wire inside a function is not allowed"),
            }
            let w = downcast_wire(&w).clone();
            assert_moduli_eq_2("assigning a wire inside a function", &r.m, &w.m);
            if DEBUG {
                println!("assign wire {} := {}, modulus {}", r.uid, &w.v, &w.m);
            }
            wires.borrow_mut()[r.uid] = Some(w);
        };
        for tc in &fun.trait_calls {
            match tc {
                Mul(r, m, w1, w2) => {
                    let w1 = read_wire(w1);
                    let w2 = read_wire(w2);
                    let w = self.mul(&m, &w1, &w2);
                    assign_wire(r, w);
                }
                Add(r, m, w1, w2) => {
                    let w1 = read_wire(w1);
                    let w2 = read_wire(w2);
                    let w = self.add(&m, &w1, &w2);
                    assign_wire(r, w);
                }
                MulC(r, m, w1, c2) => {
                    let w1 = read_wire(w1);
                    let w = self.mulc(&m, &w1, c2);
                    assign_wire(r, w);
                }
                AddC(r, m, w1, c2) => {
                    let w1 = read_wire(w1);
                    let w = self.addc(&m, &w1, c2);
                    assign_wire(r, w);
                }
                And(r, m, w1, w2) => {
                    let w1 = read_wire(w1);
                    let w2 = read_wire(w2);
                    let w = self.and(&m, &w1, &w2);
                    assign_wire(r, w);
                }
                Xor(r, m, w1, w2) => {
                    let w1 = read_wire(w1);
                    let w2 = read_wire(w2);
                    let w = self.xor(&m, &w1, &w2);
                    assign_wire(r, w);
                }
                Not(r, m, w1) => {
                    let w1 = read_wire(w1);
                    let w = self.not(&m, &w1);
                    assign_wire(r, w);
                }
                AssertZero(m, w) => {
                    let w = read_wire(w);
                    self.assert_zero(&m, &w);
                }
                Bool2Int(r, m, w1, output_modulus) => {
                    let w1 = read_wire(w1);
                    let w = self.bool2int(&m, &w1, &output_modulus);
                    assign_wire(r, w);
                }
                IntFieldSwitch(r, m, w1, output_modulus) => {
                    let w1 = read_wire(w1);
                    let w = self.int_field_switch(&m, &w1, &output_modulus);
                    assign_wire(r, w);
                }
                GetInstance(r, m) => {
                    let w = self.get_instance(&m);
                    assign_wire(r, w);
                }
                GetWitness(r, m) => {
                    let w = self.get_witness(&m);
                    assign_wire(r, w);
                }
                ZeroWire(r, m) => {
                    let w = self.zero_wire(&m);
                    assign_wire(r, w);
                }
                ConstBool(r, m, b) => {
                    let w = self.const_bool(&m, *b);
                    assign_wire(r, w);
                }
                ConstUint(r, m, c) => {
                    let w = self.const_uint(&m, c);
                    assign_wire(r, w);
                }
            }
        }
        let mut res = Vec::new();
        for r in &fun.result {
            let w = match r {
                FunWireOrConst::W(fw) => downcast_wire(&read_wire(fw)).clone(),
                FunWireOrConst::C(dw) => dw.clone(),
            };
            if DEBUG {
                println!("result: {:?}", w);
            }
            res.push(w);
        }
        if DEBUG {
            println!();
        }
        res
    }
}

impl SIEVEIR for DummyBackend {
    fn zero_wire(&self, m: &NatType) -> Wire {
        if self.inside_fn_def() {
            let w = self.new_fun_wire(m);
            self.add_trait_call(ZeroWire(w.clone(), m.clone()));
            upcast_wire(w)
        } else {
            create_wire(&get_mod(m), &Integer::zero())
        }
    }

    fn clone_wire(&self, w1: &Wire) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            let w = w1.clone();
            upcast_wire(w)
        } else {
            let v1 = view_wire(w1);
            create_wire(&v1.0, &v1.1)
        }
    }

    fn const_bool(&self, m: &NatType, b: bool) -> Wire {
        if self.inside_fn_def() {
            let w = self.new_fun_wire(m);
            self.add_trait_call(ConstBool(w.clone(), m.clone(), b));
            upcast_wire(w)
        } else {
            create_wire(&get_mod(m), &if b {Integer::one()} else {Integer::zero()})
        }
    }

    fn const_uint(&self, m: &NatType, c: &Value) -> Wire {
        if self.inside_fn_def() {
            let w = self.new_fun_wire(m);
            self.add_trait_call(ConstUint(w.clone(), m.clone(), c.clone()));
            upcast_wire(w)
        } else {
            new_variable(m, c)
        }
    }

    fn drop_wire(&self, _wire: &mut Wire) {
    }

    fn zero_wire_range(&self, m: &NatType, n: usize) -> WireRange {
        self.assert_outside_fn_def();
        let mut v = Vec::new();
        v.resize(n, Integer::zero());
        create_wr(get_mod(m), v)
    }

    fn index_wire_range(&self, wr: &WireRange, i: usize) -> Wire {
        self.assert_outside_fn_def();
        assert!(i < wr.length());
        let wr = downcast_wr(wr);
        upcast_wire(wr.index(i))
    }

    fn slice_wire_range(&self, wr: &WireRange, ir: &IndexRange) -> WireRange {
        self.assert_outside_fn_def();
        assert!(ir.first + ir.length <= wr.length());
        let (m, v) = view_wr(wr);
        create_wr(m.clone(), v[ir.first .. ir.first + ir.length].to_vec())
    }

    fn wire_to_wire_range(&self, w: &Wire) -> WireRange {
        self.assert_outside_fn_def();
        let (m, v) = view_wire(w);
        create_wr(m.clone(), vec![v.clone()])
    }

    fn clone_wire_range(&self, wr: &WireRange) -> WireRange {
        upcast_wr(downcast_wr(wr).clone())
    }

    fn drop_wire_range(&self, _wr: &mut WireRange) {
    }

    fn and(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            let w2 = downcast_fun_wire(w2);
            assert_moduli_eq("AND", m, &w1.m, &w2.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(And(w.clone(), m.clone(), w1.clone(), w2.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            assert_underlying_modulus(m, w2);
            let v1 = view_wire(w1);
            let v2 = view_wire(w2);
            assert_boolean(v1.1);
            assert_boolean(v2.1);
            assert_moduli_eq("AND", m, v1.0, v2.0);
            create_wire(v1.0, &(v1.1 * v2.1))
        }
    }

    fn xor(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            let w2 = downcast_fun_wire(w2);
            assert_moduli_eq("XOR", m, &w1.m, &w2.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(Xor(w.clone(), m.clone(), w1.clone(), w2.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            assert_underlying_modulus(m, w2);
            let v1 = view_wire(w1);
            let v2 = view_wire(w2);
            assert_boolean(v1.1);
            assert_boolean(v2.1);
            assert_moduli_eq("XOR", m, v1.0, v2.0);
            create_wire(v1.0, &if v1.1 == v2.1 {Integer::zero()} else {Integer::one()})
        }
    }

    fn not(&self, m: &NatType, w1: &Wire) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            assert_output_modulus("NOT", m, &w1.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(Not(w.clone(), m.clone(), w1.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            let v1 = view_wire(w1);
            assert_boolean(v1.1);
            assert_output_modulus("NOT", m, v1.0);
            create_wire(v1.0, &if v1.1.is_zero() {Integer::one()} else {Integer::zero()})
        }
    }

    fn mul(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            let w2 = downcast_fun_wire(w2);
            assert_moduli_eq("MUL", m, &w1.m, &w2.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(Mul(w.clone(), m.clone(), w1.clone(), w2.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            assert_underlying_modulus(m, w2);
            let v1 = view_wire(w1);
            let v2 = view_wire(w2);
            assert_moduli_eq("MUL", m, v1.0, v2.0);
            create_wire(v1.0, &((v1.1 * v2.1) % v1.0))
        }
    }

    fn add(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            let w2 = downcast_fun_wire(w2);
            assert_moduli_eq("ADD", m, &w1.m, &w2.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(Add(w.clone(), m.clone(), w1.clone(), w2.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            assert_underlying_modulus(m, w2);
            let v1 = view_wire(w1);
            let v2 = view_wire(w2);
            assert_moduli_eq("ADD", m, v1.0, v2.0);
            create_wire(v1.0, &((v1.1 + v2.1) % v1.0))
        }
    }

    fn mulc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            assert_output_modulus("MULC", m, &w1.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(MulC(w.clone(), m.clone(), w1.clone(), c2.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            let v1 = view_wire(w1);
            assert_output_modulus("MULC", m, v1.0);
            create_wire(v1.0, &((v1.1 * c2) % v1.0))
        }
    }

    fn addc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            assert_output_modulus("ADDC", m, &w1.m);
            let w = self.new_fun_wire(m);
            self.add_trait_call(AddC(w.clone(), m.clone(), w1.clone(), c2.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            let v1 = view_wire(w1);
            assert_output_modulus("ADDC", m, v1.0);
            create_wire(v1.0, &((v1.1 + c2) % v1.0))
        }
    }

    fn assert_zero(&self, m: &NatType, w: &Wire) {
        if self.inside_fn_def() {
            let w = downcast_fun_wire(w);
            assert_output_modulus("ASSERT_ZERO", m, &w.m);
            self.add_trait_call(AssertZero(m.clone(), w.clone()));
        } else {
            assert_underlying_modulus(m, w);
            let v1 = view_wire(w);
            assert_output_modulus("ASSERT_ZERO", m, v1.0);
            assert!(v1.1.is_zero(), "Assert_zero value is not zero, value: {}", v1.1);
        }
    }

    fn assert_eq_scalar_vec(&self, _m1: &NatType, _w1: &Wire, _m2: &NatType, _wires: Vec<Wire>) {
        self.assert_outside_fn_def();
        let wire_vec_view = _wires.iter().map(view_wire).collect::<Vec<(&BigInt,&BigInt)>>();
        assert!(wire_vec_view.len() > 0,"assert_eq_scalar_vec called on 0-len vector");

        assert_underlying_modulus(_m1, _w1);
        assert_underlying_modulus(_m2, _wires.first().unwrap());
        
        //assert all wires in bundle share modulus
        let first_modulus = wire_vec_view.first().unwrap().0;
        let all_eq_first = wire_vec_view.iter().all(|x| {x.0 == first_modulus});
        assert!(all_eq_first,"assert_eq_scalar_vec bundle has mixed moduli wires");

        let mut res = Integer::zero();
        let mut pow = Integer::one();
        for i in wire_vec_view {
            res += i.1*&pow;
            pow = pow*2;
        }

        let v1 = view_wire(_w1);
        assert_eq!(v1.1,&res,"assert_eq_scalar_vec result does not match expected result");
    }

    fn assert_eq(&self, _m1: &NatType, _w1: &Wire, _m2: &NatType, _w2: &Wire) {
        self.assert_outside_fn_def();
        assert_underlying_modulus(_m1, _w1);
        assert_underlying_modulus(_m2, _w2);
        let v1 = view_wire(_w1);
        let v2 = view_wire(_w2);
        assert_eq!(v1.1,v2.1,"assert_eq failed, values: {} {}",v1.1,v2.1);
    }

    /// Convert boolean wire to integer wire.
    /// TODO: We can improve on the default implementation.
    fn bool2int(&self, m: &NatType, w1: &Wire, output_modulus: &NatType) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            assert_output_modulus("BOOL2INT", m, &w1.m);
            let w = self.new_fun_wire(output_modulus);
            self.add_trait_call(Bool2Int(w.clone(), m.clone(), w1.clone(), output_modulus.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            let v1 = view_wire(w1);
            assert!(v1.1.is_zero() || v1.1.is_one(), "bool2int value is not bool {}", v1.1);
            if m.modulus == output_modulus.modulus {
                self.clone_wire(w1)
            } else {
                create_wire(&get_mod(output_modulus), &v1.1)
            }
        }
    }

    fn int_field_switch(&self, m: &NatType, w1: &Wire, output_modulus: &NatType) -> Wire {
        if self.inside_fn_def() {
            let w1 = downcast_fun_wire(w1);
            assert_output_modulus("INT_FIELD_SWITCH", m, &w1.m);
            let w = self.new_fun_wire(output_modulus);
            self.add_trait_call(IntFieldSwitch(w.clone(), m.clone(), w1.clone(), output_modulus.clone()));
            upcast_wire(w)
        } else {
            assert_underlying_modulus(m, w1);
            if m == output_modulus {
                self.clone_wire(w1)
            } else {
                let v1 = view_wire(w1);
                let modulus = get_mod(output_modulus);
                create_wire(&modulus, &(v1.1 % &modulus))
            }
        }
    }

    fn add_instance(&self, m: &NatType, x: &Value) {
        self.assert_outside_fn_def();
        self.instance_queue.borrow_mut().push_back((m.clone(), x.clone()));
    }

    fn add_witness(&self, m: &NatType, x: &Value) {
        self.assert_outside_fn_def();
        self.witness_queue.borrow_mut().push_back((m.clone(), x.clone()));
    }

    fn get_instance(&self, m: &NatType) -> Wire {
        if self.inside_fn_def() {
            let w = self.new_fun_wire(m);
            self.add_trait_call(GetInstance(w.clone(), m.clone()));
            upcast_wire(w)
        } else {
            self.assert_outside_fn_def();
            match self.instance_queue.borrow_mut().pop_front() {
                Some((m0, x)) => {
                    assert_eq!(get_mod(&m0), get_mod(m), "Moduli given to add_instance and get_instance do not match");
                    new_variable(m, &x)
                },
                None => {
                    panic!("get_instance called but instance queue empty")
                }
            }
        }
    }

    fn get_witness(&self, m: &NatType) -> Wire {
        if self.inside_fn_def() {
            let w = self.new_fun_wire(m);
            self.add_trait_call(GetWitness(w.clone(), m.clone()));
            upcast_wire(w)
        } else {
            match self.witness_queue.borrow_mut().pop_front() {
                Some((m0, x)) => {
                    assert_eq!(get_mod(&m0), get_mod(m), "Moduli given to add_witness and get_witness do not match");
                    new_variable(m, &x)
                },
                None => {
                    panic!("get_witness called but witness queue empty")
                }
            }
        }
    }

    fn get_instance_wr(&self, m: &NatType, n: usize) -> WireRange {
        self.assert_outside_fn_def();
        let mut wires: Vec<Wire> = Vec::with_capacity(n);
        for _ in 0 .. n {
            wires.push(self.get_instance(m));
        }
        create_wr_from_wires(get_mod(m), wires)
    }

    fn get_witness_wr(&self, m: &NatType, n: usize) -> WireRange {
        self.assert_outside_fn_def();
        let mut wires: Vec<Wire> = Vec::with_capacity(n);
        for _ in 0 .. n {
            wires.push(self.get_witness(m));
        }
        create_wr_from_wires(get_mod(m), wires)
    }

    fn begin_function(&self, _sieve_fn: &String, output_moduli: &Vec<&NatType>, input_moduli: Vec<&NatType>) -> (Vec<Wire>, usize) {
        let input_moduli2 = input_moduli.iter().map(|m| get_mod(m)).collect();
        let output_moduli = output_moduli.iter().map(|m| get_mod(m)).collect();
        let uid = self.begin_function_def(output_moduli, input_moduli2);
        let input_wires = input_moduli.into_iter().map(|m| upcast_wire(self.new_fun_wire(m))).collect();
        (input_wires, uid)
    }

    fn end_function(&self, wires_res: Vec<WireOrConst>) {
        self.end_function_def(wires_res);
    }

    fn apply(&self, sieve_fn: usize, _output_moduli: Vec<&NatType>, input_wires: Vec<&Wire>) -> Vec<Wire> {
        self.assert_outside_fn_def();
        if DEBUG {
            println!("Function application (uid = {}):", sieve_fn);
        }
        let fun: &Function = &self.defined_funs.borrow()[sieve_fn];
        assert_eq!(_output_moduli.len(), fun.output_moduli.len());
        for i in 0 .. _output_moduli.len() {
            assert_eq!(get_mod(_output_moduli[i]), fun.output_moduli[i]);
        }
        let input_wires = downcast_wires(input_wires);
        let res = self.apply_fn(fun, input_wires);
        upcast_wires(res)
    }

    fn create_vector(&self, m: &NatType, wocs: Vec<WireOrConst>) -> WireRange {
        let m = get_mod(m);
        let mut v: Vec<BigInt> = Vec::new();
        for woc in wocs {
            match woc {
                WireOrConst::W(w) => {
                    let w = downcast_wire(w);
                    assert_moduli_eq_2("creating a vector", &m, &w.m);
                    v.push(w.v.clone());
                }
                WireOrConst::C(c) => {
                    v.push(c.clone());
                }
            }
        }
        upcast_wr(DummyWireRange { m, v })
    }

    fn vectorized_apply(&self, sieve_fn: usize, _output_moduli: Vec<&NatType>, _input_moduli: Vec<&NatType>, _env_moduli: &Vec<NatType>, env_wires: Vec<&Wire>, wrs: Vec<&WireRange>) -> Vec<WireRange> {
        self.assert_outside_fn_def();
        if DEBUG {
            println!("Vectorized function application (uid = {}):", sieve_fn);
        }
        let fun: &Function = &self.defined_funs.borrow()[sieve_fn];

        assert_eq!(_env_moduli.len(), env_wires.len());
        assert_eq!(_input_moduli.len(), wrs.len());
        assert_eq!(_output_moduli.len(), fun.output_moduli.len());
        for i in 0 .. _output_moduli.len() {
            assert_eq!(get_mod(_output_moduli[i]), fun.output_moduli[i]);
        }
        let mut all_input_moduli = Vec::new();
        for m in _env_moduli {
            all_input_moduli.push(get_mod(m));
        }
        for m in _input_moduli {
            all_input_moduli.push(get_mod(m));
        }
        assert_eq!(all_input_moduli.len(), fun.input_moduli.len());
        for i in 0 .. all_input_moduli.len() {
            assert_eq!(all_input_moduli[i], fun.input_moduli[i]);
        }

        let env_wires = downcast_wires(env_wires);
        let wrs = downcast_wrs(wrs);
        assert!(wrs.len() > 0);
        let wr_len = wrs[0].length();
        for i in 1 .. wrs.len() {
            assert_eq!(wr_len, wrs[i].length());
        }
        let num_outputs = fun.output_moduli.len();
        let mut res: Vec<Vec<DummyWire>> = Vec::with_capacity(num_outputs);
        for _ in 0 .. num_outputs {
            res.push(Vec::with_capacity(wr_len));
        }
        let num_args = env_wires.len() + wrs.len();
        assert_eq!(num_args, fun.input_moduli.len());
        for i in 0 .. wr_len {
            if DEBUG {
                println!("Iteration {}", i);
            }
            let mut wires: Vec<DummyWire> = Vec::with_capacity(num_args);
            for w in &env_wires {
                wires.push((*w).clone());
            }
            for wr in &wrs {
                wires.push(wr.index(i));
            }
            let out_wires = self.apply_fn(fun, wires.iter().collect());
            assert_eq!(num_outputs, out_wires.len());
            out_wires.into_iter().enumerate().for_each(|(j, out_wire)| {
                res[j].push(out_wire);
            });
        }
        let res = res.into_iter().zip(fun.output_moduli.iter()).map(|(r, m)| create_wr_from_wires(m.clone(), upcast_wires(r))).collect();
        if DEBUG {
            println!("End vectorized function application (uid = {}):", sieve_fn);
            for r in &res {
                println!("Output: {:?}", r);
            }
            println!();
        }
        res
    }

    fn plugin_apply(&self, plugin: &str, operation: &str, params: Vec<&str>, modulus: &NatType, num_outputs: usize, input_wires: Vec<&Wire>) -> Vec<Wire> {
        self.assert_outside_fn_def();
        let input_wires = downcast_wires(input_wires);
        let modulus = get_mod(modulus);
        for w in &input_wires {
            assert_eq!(&modulus, &w.m, "Input modulus of an input wire of a plugin call does not match the given modulus");
        }
        let output_values: Vec<BigInt> = match plugin {
            "extended_arithmetic_v1" => {
                match operation {
                    "less_than" => {
                        assert!(params.is_empty());
                        assert_eq!(num_outputs, 1);
                        assert_eq!(input_wires.len(), 2);
                        vec![(&input_wires[0].v < &input_wires[1].v).into()]
                    }
                    "less_than_equal" => {
                        assert!(params.is_empty());
                        assert_eq!(num_outputs, 1);
                        assert_eq!(input_wires.len(), 2);
                        vec![(&input_wires[0].v <= &input_wires[1].v).into()]
                    }
                    "division" => {
                        assert!(params.is_empty());
                        assert_eq!(num_outputs, 2);
                        assert_eq!(input_wires.len(), 2);
                        let x = &input_wires[0].v;
                        let y = &input_wires[1].v;
                        vec![x / y, x % y]
                    }
                    _ => panic!("plugin_apply: unsupported extended arithmetic operation: {}", operation)
                }
            }
            _ => panic!("plugin_apply: unsupported plugin: {}", plugin)
        };
        let output_wires = output_values.into_iter().map(|v| DummyWire::new(modulus.clone(), v)).collect();
        upcast_wires(output_wires)
    }

    fn plugin_apply_wr(&self, plugin: &str, operation: &str, params: Vec<&str>, modulus: &NatType, output_counts: Vec<usize>, input_wrs: Vec<&WireRange>) -> Vec<WireRange> {
        self.assert_outside_fn_def();
        let input_wrs = downcast_wrs(input_wrs);
        let modulus = get_mod(modulus);
        for wr in &input_wrs {
            assert_eq!(&modulus, &wr.m, "Input modulus of an input wire range of a plugin call does not match the given modulus");
        }
        let output_values: Vec<Vec<BigInt>> = match plugin {
            "extended_arithmetic_v1" => {
                match operation {
                    "bit_decompose" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        let bw = output_counts[0];
                        assert_eq!(input_wrs.len(), 1);
                        let input_wr = input_wrs[0];
                        assert_eq!(input_wr.v.len(), 1);
                        let x = &input_wr.v[0];
                        let mut bits: Vec<BigInt> = Vec::new();
                        for i in 0 .. bw {
                            let b = x.bit(i.to_u64().unwrap());
                            if b {
                                bits.push(BigInt::one());
                            } else {
                                bits.push(BigInt::zero());
                            }
                        }
                        bits = bits.into_iter().rev().collect();
                        vec![bits]
                    }
                    _ => panic!("plugin_apply_wr: unsupported extended arithmetic operation: {}", operation)
                }
            }
            "vectors_v1" => {
                match operation {
                    "add" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        let n = output_counts[0];
                        assert_eq!(input_wrs.len(), 2);
                        let xs = &input_wrs[0].v;
                        let ys = &input_wrs[1].v;
                        assert_eq!(xs.len(), ys.len());
                        assert_eq!(xs.len(), n);
                        let zs = xs.iter().zip(ys.iter()).map(|(x, y)| (x + y) % &modulus).collect();
                        vec![zs]
                    }
                    "mul" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        let n = output_counts[0];
                        assert_eq!(input_wrs.len(), 2);
                        let xs = &input_wrs[0].v;
                        let ys = &input_wrs[1].v;
                        assert_eq!(xs.len(), ys.len());
                        assert_eq!(xs.len(), n);
                        let zs = xs.iter().zip(ys.iter()).map(|(x, y)| (x * y) % &modulus).collect();
                        vec![zs]
                    }
                    "add_scalar" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        let n = output_counts[0];
                        assert_eq!(input_wrs.len(), 2);
                        let xs = &input_wrs[0].v;
                        let ys = &input_wrs[1].v;
                        assert_eq!(xs.len(), n);
                        assert_eq!(ys.len(), 1);
                        let y = &ys[0];
                        let zs = xs.iter().map(|x| (x + y) % &modulus).collect();
                        vec![zs]
                    }
                    "mul_scalar" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        let n = output_counts[0];
                        assert_eq!(input_wrs.len(), 2);
                        let xs = &input_wrs[0].v;
                        let ys = &input_wrs[1].v;
                        assert_eq!(xs.len(), n);
                        assert_eq!(ys.len(), 1);
                        let y = &ys[0];
                        let zs = xs.iter().map(|x| (x * y) % &modulus).collect();
                        vec![zs]
                    }
                    "addc" => {
                        assert_eq!(params.len(), 1);
                        let c = params[0];
                        let c = BigInt::parse_bytes(c.as_bytes(), 10).expect("The string parameter of addc must be a decimal representation of an integer");
                        assert!(&c >= &BigInt::zero(), "The string parameter of addc must be nonnegative");
                        assert!(&c < &modulus, "The string parameter of addc must be less than the modulus");
                        assert_eq!(output_counts.len(), 1);
                        let n = output_counts[0];
                        assert_eq!(input_wrs.len(), 1);
                        let xs = &input_wrs[0].v;
                        assert_eq!(xs.len(), n);
                        let zs = xs.iter().map(|x| (x + &c) % &modulus).collect();
                        vec![zs]
                    }
                    "mulc" => {
                        assert_eq!(params.len(), 1);
                        let c = params[0];
                        let c = BigInt::parse_bytes(c.as_bytes(), 10).expect("The string parameter of mulc must be a decimal representation of an integer");
                        assert!(&c >= &BigInt::zero(), "The string parameter of mulc must be nonnegative");
                        assert!(&c < &modulus, "The string parameter of mulc must be less than the modulus");
                        assert_eq!(output_counts.len(), 1);
                        let n = output_counts[0];
                        assert_eq!(input_wrs.len(), 1);
                        let xs = &input_wrs[0].v;
                        assert_eq!(xs.len(), n);
                        let zs = xs.iter().map(|x| (x * &c) % &modulus).collect();
                        vec![zs]
                    }
                    "sum" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        assert_eq!(output_counts[0], 1);
                        assert_eq!(input_wrs.len(), 1);
                        let xs = &input_wrs[0].v;
                        let mut s = BigInt::zero();
                        for x in xs {
                            s = s + x;
                        }
                        vec![vec![s]]
                    }
                    "product" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        assert_eq!(output_counts[0], 1);
                        assert_eq!(input_wrs.len(), 1);
                        let xs = &input_wrs[0].v;
                        let mut s = BigInt::one();
                        for x in xs {
                            s = s * x;
                        }
                        vec![vec![s]]
                    }
                    "dotproduct" => {
                        assert!(params.is_empty());
                        assert_eq!(output_counts.len(), 1);
                        assert_eq!(output_counts[0], 1);
                        assert_eq!(input_wrs.len(), 2);
                        let xs = &input_wrs[0].v;
                        let ys = &input_wrs[1].v;
                        assert_eq!(xs.len(), ys.len());
                        let mut s = BigInt::zero();
                        for (x, y) in xs.iter().zip(ys.iter()) {
                            s = s + x * y;
                        }
                        vec![vec![s]]
                    }
                    _ => panic!("plugin_apply_wr: unsupported vectors plugin operation: {}", operation)
                }
            }
            "permutation_check_v1" => {
                match operation {
                    "assert_perm" => {
                        assert_eq!(params.len(), 1);
                        let tuple_len = params[0];
                        let tuple_len = BigInt::parse_bytes(tuple_len.as_bytes(), 10).expect("The string parameter of assert_perm must be a decimal representation of an integer");
                        let tuple_len: usize = tuple_len.try_into().expect("The string parameter of assert_perm does not fit into usize");
                        assert!(tuple_len > 0, "The string parameter of assert_perm must be positive");
                        assert_eq!(output_counts.len(), 0);
                        assert_eq!(input_wrs.len(), 2);
                        let xs_pre = &input_wrs[0].v;
                        let ys_pre = &input_wrs[1].v;
                        assert_eq!(xs_pre.len(), ys_pre.len());
                        assert!(xs_pre.len() % tuple_len == 0, "Length of the input vectors must be divisible by the tuple length");
                        let mut xv = Vec::new();
                        let mut yv = Vec::new();
                        let mut xt = Vec::new();
                        let mut yt = Vec::new();
                        for (x, y) in xs_pre.iter().zip(ys_pre.iter()) {
                            xt.push(x);
                            yt.push(y);
                            if xt.len() >= tuple_len {
                                xv.push(xt);
                                xt = Vec::new();
                                yv.push(yt);
                                yt = Vec::new();
                            }
                        }
                        xv.sort();
                        yv.sort();
                        assert!(xv == yv, "assert_perm: argument lists of tuples are not permutations of each other");
                        vec![]
                    }
                    _ => panic!("plugin_apply_wr: unsupported permutation check plugin operation: {}", operation)
                }
            }
            _ => panic!("plugin_apply_wr: unsupported plugin: {}", plugin)
        };
        let output_wrs = output_values.into_iter().map(|v| DummyWireRange::new(modulus.clone(), v)).collect();
        upcast_wrs(output_wrs)
    }

    fn switch_apply(&self, sieve_fns: &Vec<usize>, default_sieve_fn: usize, ints: &Vec<Integer>, w_modulus: &NatType,
                output_moduli: Vec<&NatType>, input_moduli: Vec<&NatType>, w: &Wire, wires: Vec<&Wire>, witness_count: u64) -> Vec<Wire> {
        self.assert_outside_fn_def();
        let w = downcast_wire(w);
        let wires = downcast_wires(wires);
        let output_moduli: Vec<_> = output_moduli.into_iter().map(|m| get_mod(m)).collect();
        let input_moduli: Vec<_> = input_moduli.into_iter().map(|m| get_mod(m)).collect();
        let mut all_sieve_fns = sieve_fns.clone();
        all_sieve_fns.push(default_sieve_fn);
        for sieve_fn in all_sieve_fns {
            let fun: &Function = &self.defined_funs.borrow()[sieve_fn];
            assert_eq!(output_moduli.len(), fun.output_moduli.len());
            for i in 0 .. output_moduli.len() {
                assert_eq!(output_moduli[i], fun.output_moduli[i]);
            }
            assert_eq!(input_moduli.len(), fun.input_moduli.len());
            for i in 0 .. input_moduli.len() {
                assert_eq!(input_moduli[i], fun.input_moduli[i]);
            }
            assert!(fun.witness_count <= witness_count);
        }
        let w_modulus = get_mod(w_modulus);
        let mut chosen_fn = default_sieve_fn;
        for i in ints {
            assert!(i >= &BigInt::zero(), "The integers in disjunction plugin branches must be nonnegative");
            assert!(i < &w_modulus, "The integers in disjunction plugin branches must be less than the modulus");
        }
        for (i, sieve_fn) in ints.iter().zip(sieve_fns.iter()) {
            if &w.v == i {
                chosen_fn = *sieve_fn;
                break;
            }
        }
        let fun: &Function = &self.defined_funs.borrow()[chosen_fn];
        let num_extra_witnesses = witness_count - fun.witness_count;
        let res = self.apply_fn(fun, wires);
        for _ in 0 .. num_extra_witnesses {
            match self.witness_queue.borrow_mut().pop_front() {
                Some(_) => {}
                None => panic!("disjunction plugin: expected padded witness but witness queue empty"),
            }
        }
        upcast_wires(res)
    }
}
