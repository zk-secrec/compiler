/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use std::fmt;
use std::fmt::Debug;
use std::rc::Rc;
use std::any::Any;
use num_traits::{Zero, One};

use crate::integer::*;
use crate::value::Value;
use crate::zksc_types::*;

pub trait AllocationTrait {
    fn to_any(&self) -> &dyn Any;
}

pub struct Allocation(Box<dyn AllocationTrait>);

impl Allocation {
    pub fn new<T : AllocationTrait + 'static>(x : T) -> Allocation {
        Allocation(Box::new(x))
    }

    pub fn downcast<T : AllocationTrait + 'static>(&self) -> &T {
        if let Some(x) = self.0.to_any().downcast_ref::<T>() {
            x
        } else {
            panic!("Attempting to downcast an Allocation to a wrong implementation of AllocationTrait");
        }
    }
}

pub trait WireTrait: Debug {
    fn to_any(&self) -> &dyn Any;
}

#[derive(Debug)]
pub struct Wire(Box<dyn WireTrait>);

impl Clone for Wire {
    fn clone(&self) -> Self {
        sieve_backend().clone_wire(self)
    }
}

impl Drop for Wire {
    fn drop(&mut self) {
        sieve_backend().drop_wire(self);
    }
}

impl Wire {
    pub fn new<T : WireTrait + 'static>(x : T) -> Wire {
        Wire(Box::new(x))
    }

    pub fn downcast<T : WireTrait + 'static>(&self) -> &T {
        if let Some(x) = self.0.to_any().downcast_ref::<T>() {
            x
        } else {
            panic!("Attempting to downcast a Wire to a wrong implementation of WireTrait");
        }
    }
}

#[derive(Clone, Debug)]
pub struct IndexRange {
    pub first: usize,
    pub length: usize,
}

impl IndexRange {
    pub fn index(&self, i: usize) -> usize {
        assert!(i < self.length);
        self.first + i
    }
}

pub trait WireRangeTrait: Debug {
    fn length(&self) -> usize;
    fn to_any(&self) -> &dyn Any;
}

#[derive(Debug)]
pub struct WireRange(Box<dyn WireRangeTrait>);

impl Clone for WireRange {
    fn clone(&self) -> Self {
        sieve_backend().clone_wire_range(self)
    }
}

impl Drop for WireRange {
    fn drop(&mut self) {
        sieve_backend().drop_wire_range(self);
    }
}

impl WireRange {
    pub fn new<T : WireRangeTrait + 'static>(x : T) -> WireRange {
        WireRange(Box::new(x))
    }

    pub fn downcast<T : WireRangeTrait + 'static>(&self) -> &T {
        if let Some(x) = self.0.to_any().downcast_ref::<T>() {
            x
        } else {
            panic!("Attempting to downcast a WireRange to a wrong implementation of WireRangeTrait");
        }
    }

    pub fn length(&self) -> usize {
        self.0.length()
    }

    pub fn index(&self, i: usize) -> Wire {
        sieve_backend().index_wire_range(self, i)
    }

    pub fn slice(&self, ir: &IndexRange) -> WireRange {
        sieve_backend().slice_wire_range(self, ir)
    }
}

pub fn upcast_wire<T : WireTrait + 'static>(x : T) -> Wire {
    Wire::new(x)
}

pub fn upcast_wires<T : WireTrait + 'static>(x : Vec<T>) -> Vec<Wire> {
    x.into_iter().map(|x| upcast_wire(x)).collect()
}

pub fn upcast_wr<T : WireRangeTrait + 'static>(x : T) -> WireRange {
    WireRange::new(x)
}

pub fn upcast_wrs<T : WireRangeTrait + 'static>(x : Vec<T>) -> Vec<WireRange> {
    x.into_iter().map(|x| upcast_wr(x)).collect()
}

pub fn wire_to_wr(w: &Wire) -> WireRange {
    sieve_backend().wire_to_wire_range(w)
}

// For backends that do not support wire ranges
#[derive(Clone, Debug)]
struct SimpleWireRange(Vec<Wire>);

impl WireRangeTrait for SimpleWireRange {
    fn length(&self) -> usize {
        self.0.len()
    }

    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

fn downcast_simple_wr(wr: &WireRange) -> &SimpleWireRange {
    wr.downcast::<SimpleWireRange>()
}

pub enum WireOrConst<'a> {
    W(&'a Wire),
    C(Integer),
}

pub enum WireOrConstOwned {
    W(Wire),
    C(Integer),
}

pub type LinearCombination<W> = Vec<(W, Integer)>;

// R1CS constraint
// a * b = c
pub struct Constraint<W> {
    pub a: LinearCombination<W>,
    pub b: LinearCombination<W>,
    pub c: LinearCombination<W>,
}

pub trait SIEVEIR {
    /// Write SIEVE IR headers if they could not be written yet
    /// when the struct implementing this trait was allocated.
    /// ns is the list of fields used in the circuit.
    /// supported_conversions is the list of conversions between fields supported in the circuit,
    /// the first element of the pair is the input field and the second element is the output field of the conversion.
    /// supported_plugins is the list of names of supported plugins.
    fn write_headers(&self, _ns: &Vec<NatType>, _supported_conversions: Vec<(&NatType, &NatType)>, _supported_plugins: Vec<&str>) {}

    /// Construct wire that won't be used.
    fn zero_wire(&self, _m: &NatType) -> Wire;

    /// Clone a wire.
    /// Both input and output wire will be deallocated separately.
    /// If the underlying wire representation is a raw pointer the clone will have
    /// to either copy the pointed data or deal with reference counting.
    /// Input and output have the same modulus.
    fn clone_wire(&self, w1: &Wire) -> Wire;

    /// Deallocate a wire.
    fn drop_wire(&self, wire: &mut Wire);

    /// Construct a wire range of length n that won't be used.
    fn zero_wire_range(&self, m: &NatType, n: usize) -> WireRange {
        let mut xs: Vec<Wire> = Vec::with_capacity(n);
        for _ in 0 .. n {
            xs.push(self.zero_wire(m));
        }
        upcast_wr(SimpleWireRange(xs))
    }

    /// Clone a range of wires.
    fn clone_wire_range(&self, _wr: &WireRange) -> WireRange {
        unimplemented!("Backend does not support wire ranges.")
    }

    /// Index a range of wires.
    fn index_wire_range(&self, wr: &WireRange, i: usize) -> Wire {
        let wr = downcast_simple_wr(wr);
        wr.0[i].clone()
    }

    /// Slice a range of wires.
    fn slice_wire_range(&self, _wr: &WireRange, _ir: &IndexRange) -> WireRange {
        unimplemented!("Backend does not support wire ranges.")
    }

    /// Convert a wire into a length-1 wire range.
    fn wire_to_wire_range(&self, _w: &Wire) -> WireRange {
        unimplemented!("Backend does not support wire ranges.")
    }

    /// Drop a wire range. Called automatically when the wire range goes out of scope.
    /// This method should free any memory that is not freed automatically.
    fn drop_wire_range(&self, _wr: &mut WireRange) {}

    /// Allocate a range of wires.
    fn declare_new_wire_range(&self, _alloc: &Allocation) {
        unimplemented!("Backend does not support explicitly allocating wire ranges.")
    }

    /// Deallocate a range of wires.
    fn declare_delete_wire_range(&self, _alloc: &Allocation) {
        unimplemented!("Backend does not support deleting wire ranges.")
    }

    /// Logical conjuction.
    fn and(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire;

    /// Logical exclusive or.
    fn xor(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire;

    /// Logical negation.
    fn not(&self, m: &NatType, w1: &Wire) -> Wire;

    /// Load a constant booleans onto a fresh wire.
    fn const_bool(&self, m: &NatType, b: bool) -> Wire;

    /// Modular multiplication.
    fn mul(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire;

    /// Modular addition.
    fn add(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire;

    /// Modular subtraction.
    /// Some backends may support it more efficiently than multiplying by -1 and adding.
    /// Multiplying by -1 can be slow for large moduli.
    fn sub(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let modulus = match m.modulus {
            Some(ref m) => m,
            _ => panic!("Infinite modulus not supported in $post"),
        };
        let w2_neg = self.mulc(m, w2, &(modulus - 1));
        self.add(m, w1, &w2_neg)
    }

    /// Modular multiplication between value on wire and constant value.
    fn mulc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire;

    /// Modular multiplication between value on wire and a verifier's value.
    fn mulv(&self, _m: &NatType, _w1: &Wire, _c2: &Value) -> Wire {
        unimplemented!("Backend does not support mulv.")
    }

    /// Modular addition between value on wire and constant value.
    fn addc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire;

    /// Modular subtraction of a value on wire from a constant value.
    fn subc(&self, m: &NatType, c1: &Integer, w2: &Wire) -> Wire {
        let modulus = match m.modulus {
            Some(ref m) => m,
            _ => panic!("Infinite modulus not supported in $post"),
        };
        let w2_neg = self.mulc(m, w2, &(modulus - 1));
        self.addc(m, &w2_neg, c1)
    }

    /// Bitwise shift left of a wire by a constant value.
    fn shlc(&self, _m: &NatType, _w1: &Wire, _c2: u64) -> Wire {
        unimplemented!("Backend does not support bitwise shifts.")
    }

    /// Bitwise shift right of a wire by a constant value.
    fn shrc(&self, _m: &NatType, _w1: &Wire, _c2: u64) -> Wire {
        unimplemented!("Backend does not support bitwise shifts.")
    }

    /// Converts a vector of bitwise elements from one bitwise ring to another.
    /// The conversion is big-endian, i.e. the first element of the smaller ring
    /// corresponds to the highest bits of the first element of the larger ring.
    /// If the total number of bits in the first vector is not a multiple of
    /// the number of bits in the seconds ring then the last element of the output vector
    /// is padded with zeros as the lowest bits.
    fn bitwise_vec_to_bitwise_vec(&self, _m1: &NatType, _m2: &NatType, _wr1: &WireRange) -> WireRange {
        unimplemented!("Backend does not support bitwise vector conversion.")
    }

    /// Transposes a bit matrix `wr1` of `nr` values of `nc` bits each
    /// into a transposed bit matrix of `nc` values of `nr` bits each.
    fn bit_matrix_transpose(&self, _m1: &NatType, _m2: &NatType, _wr1: &WireRange, _nr: u64, _nc: u64) -> WireRange {
        unimplemented!("Backend does not support bit matrix transposition.")
    }

    /// Concatenates two vectors, obtaining a new vector.
    fn concat_vec(&self, _m: &NatType, _wr1: &WireRange, _wr2: &WireRange) -> WireRange {
        unimplemented!("Backend does not support vector concatenation.")
    }

    /// ECDSA verification. Some inputs are read from instance.
    fn ecdsa_verification(&self, _m: &NatType, _bits_per_block: u64, _scalar1: &Wire, _scalar2: &Wire, _r_x: &Wire, _r_y: &Wire) {
        unimplemented!("Backend does not support ECDSA verification.")
    }

    /// Assert that the value on the wire is zero.
    fn assert_zero(&self, m: &NatType, w: &Wire);

    /// Begin a SIEVE IR function definition.
    /// Returns wires corresponding to the inputs
    /// and a UID for the SIEVE IR function (which must be different each time begin_function is called).
    fn begin_function(&self, _sieve_fn: &String, _output_moduli: &Vec<&NatType>, _input_moduli: Vec<&NatType>) -> (Vec<Wire>, usize) {
        unimplemented!("Backend does not support functions.")
    }

    /// End a SIEVE IR function definition.
    /// wires_res are the wires where the result was computed.
    fn end_function(&self, _wires_res: Vec<WireOrConst>) {
        unimplemented!("Backend does not support functions.")
    }

    /// Copy wires or constant values to wires with consecutive numbers,
    /// so that they can be used in vectorized operations
    fn create_vector(&self, _m: &NatType, _wocs: Vec<WireOrConst>) -> WireRange {
        unimplemented!("Backend does not support vectorized operations.")
    }

    /// Apply a SIEVE IR function with the given uid in a non-vectorized way
    /// to the values on the input wires.
    fn apply(&self, _uid: usize, _output_moduli: Vec<&NatType>, _input_wires: Vec<&Wire>) -> Vec<Wire> {
        unimplemented!("Backend does not support function calls.")
    }

    /// Apply one of the SIEVE IR functions with uids in sieve_fns in a non-vectorized way
    /// to the values on the input wires.
    /// The disjunction plugin is used to choose which function to apply according to
    /// which value in ints (if any) the value on wire w is equal to.
    /// If is is not equal to any, the default function (with uid default_sieve_fn) is chosen.
    fn switch_apply(&self, _sieve_fns: &Vec<usize>, _default_sieve_fn: usize, _ints: &Vec<Integer>, _w_modulus: &NatType,
                _output_moduli: Vec<&NatType>, _input_moduli: Vec<&NatType>, _w: &Wire, _wires: Vec<&Wire>, _witness_count: u64) -> Vec<Wire> {
        unimplemented!("Backend does not support the disjunction plugin.")
    }

    /// Apply a SIEVE IR function with the given uid in a vectorized way
    /// to the values on the input wire ranges.
    fn vectorized_apply(&self, _uid: usize, _output_moduli: Vec<&NatType>, _input_moduli: Vec<&NatType>, _env_moduli: &Vec<NatType>, _env_wires: Vec<&Wire>, _wrs: Vec<&WireRange>) -> Vec<WireRange> {
        unimplemented!("Backend does not support vectorized operations.")
    }

    /// Apply a plugin operation that uses a single modulus and has single wires as inputs and outputs.
    fn plugin_apply(&self, _plugin: &str, _operation: &str, _params: Vec<&str>, _modulus: &NatType, _num_outputs: usize, _input_wires: Vec<&Wire>) -> Vec<Wire> {
        unimplemented!("Backend does not support plugins.")
    }

    /// Apply a plugin operation that uses a single modulus and has wire ranges as inputs and outputs.
    fn plugin_apply_wr(&self, _plugin: &str, _operation: &str, _params: Vec<&str>, _modulus: &NatType, _output_counts: Vec<usize>, _input_wrs: Vec<&WireRange>) -> Vec<WireRange> {
        unimplemented!("Backend does not support plugins.")
    }

    /// Convert boolean wire to integer wire.
    /// TODO: We can improve on the default implementation.
    fn bool2int(&self, m: &NatType, w1: &Wire, output_modulus: &NatType) -> Wire {
        if m.modulus == output_modulus.modulus {
            self.clone_wire(w1)
        } else {
            unimplemented!("Backend does not support field switching.")
        }
    }

    /// Semantically identical to `clone_wire` where wires have modulus `2`.
    /// Internally used to make sure that textual IR1 output is identical to our earlier versions.
    fn copy_bool(&self, _m: &NatType, w1: &Wire) -> Wire {
        self.clone_wire(w1)
    }

    /// Assert that values on two wires (of different moduli) are equal.
    fn assert_eq(&self, _m1: &NatType, _w1: &Wire, _m2: &NatType, _w2: &Wire) {
        unimplemented!("Backend does not support field switching with assert_eq.");
    }

    /// Assert that the value of `w1` has binary representation based on values of `wires`.
    /// value(w1) = value(wires[0]) + 2*value(wires[1]) + 4*value(wires[2]) + ...
    /// Used for more efficiently implemement booleans circuit evaluation.
    fn assert_eq_scalar_vec(&self, m1: &NatType, w1: &Wire, m2: &NatType, wires: Vec<Wire>);

    /// This should return true if the backend supports assert_eq for arguments of rings `m1` and `m2`
    /// but not direct conversion from `m1` to `m2`.
    /// Then the direct conversion will be automatically implemented thru assert_eq.
    fn ring_switch_thru_assert_eq(&self, _m1: &NatType, _m2: &NatType) -> bool {
        return false;
    }

    /// Helper method for assert_r1cs_constraint.
    fn add_wocs(&self, m: &NatType, woc1: WireOrConstOwned, woc2: WireOrConstOwned) -> WireOrConstOwned {
        match (woc1, woc2) {
            (WireOrConstOwned::W(w1), WireOrConstOwned::W(w2)) => WireOrConstOwned::W(self.add(m, &w1, &w2)),
            (WireOrConstOwned::W(w1), WireOrConstOwned::C(c2)) => WireOrConstOwned::W(if c2.is_zero() { w1 } else { self.addc(m, &w1, &c2) }),
            (WireOrConstOwned::C(c1), WireOrConstOwned::W(w2)) => WireOrConstOwned::W(if c1.is_zero() { w2 } else { self.addc(m, &w2, &c1) }),
            (WireOrConstOwned::C(c1), WireOrConstOwned::C(c2)) => WireOrConstOwned::C((c1 + c2) % m.modulus.as_ref().unwrap()),
        }
    }

    /// Helper method for assert_r1cs_constraint.
    fn sub_or_negated_sub_wocs(&self, m: &NatType, woc1: WireOrConstOwned, woc2: WireOrConstOwned) -> WireOrConstOwned {
        let modulus = m.modulus.as_ref().unwrap();
        match (woc1, woc2) {
            (WireOrConstOwned::W(w1), WireOrConstOwned::W(w2)) => WireOrConstOwned::W(self.sub(m, &w1, &w2)),
            (WireOrConstOwned::W(w1), WireOrConstOwned::C(c2)) => WireOrConstOwned::W(if c2.is_zero() { w1 } else { self.addc(m, &w1, &((modulus - c2) % modulus)) }),
            (WireOrConstOwned::C(c1), WireOrConstOwned::W(w2)) => WireOrConstOwned::W(if c1.is_zero() { w2 } else { self.addc(m, &w2, &((modulus - c1) % modulus)) }), // negated sub here, as it is more efficient
            (WireOrConstOwned::C(c1), WireOrConstOwned::C(c2)) => WireOrConstOwned::C((modulus + c1 - c2) % modulus),
        }
    }

    /// Helper method for assert_r1cs_constraint.
    fn mul_wocs(&self, m: &NatType, woc1: WireOrConstOwned, woc2: WireOrConstOwned) -> WireOrConstOwned {
        match (woc1, woc2) {
            (WireOrConstOwned::W(w1), WireOrConstOwned::W(w2)) => WireOrConstOwned::W(self.mul(m, &w1, &w2)),
            (WireOrConstOwned::W(w1), WireOrConstOwned::C(c2)) => WireOrConstOwned::W(if c2.is_one() { w1 } else { self.mulc(m, &w1, &c2) }),
            (WireOrConstOwned::C(c1), WireOrConstOwned::W(w2)) => WireOrConstOwned::W(if c1.is_one() { w2 } else { self.mulc(m, &w2, &c1) }),
            (WireOrConstOwned::C(c1), WireOrConstOwned::C(c2)) => WireOrConstOwned::C((c1 * c2) % m.modulus.as_ref().unwrap()),
        }
    }

    /// Helper method for assert_r1cs_constraint.
    fn compute_linear_combination(&self, m: &NatType, lc: &LinearCombination<Option<Wire>>) -> WireOrConstOwned {
        let mut sum = WireOrConstOwned::C(Integer::zero());
        for (w, c) in lc {
            let x = match w {
                None => WireOrConstOwned::C(c.clone()),
                Some(w) => WireOrConstOwned::W(if c.is_one() { w.clone() } else { self.mulc(m, w, c) }),
            };
            sum = self.add_wocs(m, sum, x);
        }
        sum
    }

    /// Assert that an R1CS constraint over wires (and the constant 1) holds.
    /// Each wire w is wrapped into Some(w).
    /// None represents the constant 1.
    fn assert_r1cs_constraint(&self, m: &NatType, c: &Constraint<Option<Wire>>) {
        let x1 = self.compute_linear_combination(m, &c.a);
        let x2 = self.compute_linear_combination(m, &c.b);
        let x3 = self.compute_linear_combination(m, &c.c);
        let x = self.sub_or_negated_sub_wocs(m, self.mul_wocs(m, x1, x2), x3);
        match x {
            WireOrConstOwned::W(x) => self.assert_zero(m, &x),
            WireOrConstOwned::C(c) => assert!(c.is_zero()),
        }
    }

    /// Switch the field of `w1` to new modulus `m`.
    /// For conversion of boolean to uint we use bool2int calls instead.
    fn int_field_switch(&self, m: &NatType, w1: &Wire, output_modulus: &NatType) -> Wire {
        if m == output_modulus {
            self.clone_wire(w1)
        }
        else {
            unimplemented!("Backend does not support field switching.")
        }
    }

    /// TODO: Document. Do not use Value here.
    /// Add a new value `x` to the instance stream of modulus `m`.
    fn add_instance(&self, _m: &NatType, _x: &Value) {
        unimplemented!("Backend does not support instance/witness.")
    }

    /// Get value of a new wire from the instance stream of modulus `m`.
    /// This function is called sequentially so n-th call loads the n-th value from the instance.
    /// The value must be added to the instance using add_instance before it can be read
    /// with get_instance or get_instance_wr.
    fn get_instance(&self, _m: &NatType) -> Wire {
        unimplemented!("Backend does not support instance/witness.")
    }

    /// Get `n` values from instance to a new wire range.
    /// This is equivalent to calling get_instance `n` times
    /// but may be more efficient if the backend supports vectorized get_instance.
    /// The `n` values must be added to the instance stream using add_instance
    /// before they can be read with get_instance_wr.
    fn get_instance_wr(&self, m: &NatType, n: usize) -> WireRange {
        let mut xs: Vec<Wire> = Vec::with_capacity(n);
        for _ in 0 .. n {
            xs.push(self.get_instance(m));
        }
        upcast_wr(SimpleWireRange(xs))
    }

    /// TODO: Document. Do not use Value here.
    /// Add a new value `x` to the witness stream of modulus `m`.
    fn add_witness(&self, _m: &NatType, _x: &Value) {
        unimplemented!("Backend does not support instance/witness.")
    }

    /// Get value of a new wire from the witness stream of modulus `m`.
    /// This function is called sequentially so n-th call loads the n-th value from the witness.
    /// The value must be added to the witness using add_witness before it can be read
    /// with get_witness or get_witness_wr.
    fn get_witness(&self, _m: &NatType) -> Wire {
        unimplemented!("Backend does not support instance/witness.")
    }

    /// Get `n` values from witness to a new wire range.
    /// This is equivalent to calling get_witness `n` times
    /// but may be more efficient if the backend supports vectorized get_witness.
    /// The `n` values must be added to the witness stream using add_witness
    /// before they can be read with get_witness_wr.
    fn get_witness_wr(&self, m: &NatType, n: usize) -> WireRange {
        let mut xs: Vec<Wire> = Vec::with_capacity(n);
        for _ in 0 .. n {
            xs.push(self.get_witness(m));
        }
        upcast_wr(SimpleWireRange(xs))
    }

    /// Assign a constant to a wire.
    /// Similar to add_instance+get_instance and add_witness+get_witness but for public values.
    fn const_uint(&self, _m: &NatType, _x: &Value) -> Wire {
        unimplemented!("Backend does not support const_uint");
    }

    /// For profiling how many wires are used in each part of the code.
    fn get_next_wire_number(&self) -> u64 {
        0 // return arbitrary value to avoid failing if the backend does not support this
    }

    /// For profiling how many lines of relation file are generated in each part of the code.
    fn get_rel_file_size(&self) -> u64 {
        0 // return arbitrary value to avoid failing if the backend does not support this
    }

    /// Flush output.
    /// Useful for text-based implementations like IR1 output.
    fn flush(&self) {}

    /// Signal that code execution is finished.
    fn finalize(&self) {}

    fn current_status(&self) -> bool {
        true
    }
}

static mut SIEVE_BACKEND: &dyn SIEVEIR = &NopSieveBackend;

pub fn set_sieve_backend(backend: &'static dyn SIEVEIR) {
    unsafe {
        SIEVE_BACKEND = backend;
    }
}

pub fn set_boxed_sieve_backend(backend: Box<dyn SIEVEIR>) {
    set_sieve_backend(Box::leak(backend));
}

pub fn sieve_backend() -> &'static dyn SIEVEIR {
    unsafe { SIEVE_BACKEND }
}

///
pub struct BigIntDecimalDisplay<'a> {
    inner: &'a [usize]
}

impl<'a> BigIntDecimalDisplay<'a> {
    fn new(inner: &'a [usize]) -> BigIntDecimalDisplay<'a> {
        BigIntDecimalDisplay { inner }
    }
}


#[cfg(any(target_pointer_width="32",target_pointer_width="16",target_pointer_width="8"))]
fn iter_u32(x: &usize) -> impl Iterator<Item = u32> {
    std::iter::once(*x as u32)
}

#[cfg(target_pointer_width="64")]
fn iter_u32(x: &usize) -> impl Iterator<Item = u32> {
    const MASK : usize = u32::MAX as usize;
    [(*x & MASK) as u32, ((*x >> 32) & MASK) as u32].into_iter()
}

impl<'a> fmt::Display for BigIntDecimalDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = self.inner;
        match slice.len() {
            0 => f.write_str("0"),
            1 => write!(f, "{}", slice[0]),
            _ => {
                let vec : Vec<u32> = slice.iter().flat_map(iter_u32).collect();
                let bigint = num_bigint::BigUint::new(vec);
                write!(f, "{}", bigint)
            }
        }
    }
}

struct NopSieveBackend;

#[derive(Clone, Debug)]
struct NopWire;

impl WireTrait for NopWire {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl SIEVEIR for NopSieveBackend {
    fn zero_wire(&self, _m: &NatType) -> Wire {
        upcast_wire(NopWire)
    }

    fn clone_wire(&self, _w1: &Wire) -> Wire {
        upcast_wire(NopWire)
    }

    fn const_bool(&self, _m: &NatType, _w1: bool) -> Wire {
        self.zero_wire(_m)
    }

    fn drop_wire(&self, _wire: &mut Wire) {}

    fn and(&self, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {
        self.zero_wire(_m)
    }

    fn xor(&self, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {
        self.zero_wire(_m)
    }

    fn not(&self, _m: &NatType, _w1: &Wire) -> Wire {
        self.zero_wire(_m)
    }

    fn mul(&self, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {
        self.zero_wire(_m)
    }

    fn add(&self, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {
        self.zero_wire(_m)
    }

    fn mulc(&self, _m: &NatType, _w1: &Wire, _c2: &Integer) -> Wire {
        self.zero_wire(_m)
    }

    fn addc(&self, _m: &NatType, _w1: &Wire, _c2: &Integer) -> Wire {
        self.zero_wire(_m)
    }

    fn assert_zero(&self, _m: &NatType, _w: &Wire) {}

    fn assert_eq_scalar_vec(&self, _m1: &NatType, _w1: &Wire, _m2: &NatType, _wires: Vec<Wire>) {}

    fn get_instance(&self, m: &NatType) -> Wire { self.zero_wire(m) }

    fn get_witness(&self, m: &NatType) -> Wire { self.zero_wire(m) }

    fn add_instance(&self, _m: &NatType, _x: &Value) {}

    fn add_witness(&self, _m: &NatType, _x: &Value) {}
}

pub trait ChallengeBackend {
    fn challenge(&self, _ctx: &dyn SIEVEIR, _m: &NatType, _n: usize) -> Value;

    fn read_witness_confirmation(&self, _ctx: &dyn SIEVEIR);

    fn read_emp_line_1(&self);
}

struct UnimplementedChallengeBackend;

impl ChallengeBackend for UnimplementedChallengeBackend {
    fn challenge(&self, _ctx: &dyn SIEVEIR, _m: &NatType, _n: usize) -> Value {
        unimplemented!("Backend does not support interactive challenges.")
    }

    fn read_witness_confirmation(&self, _ctx: &dyn SIEVEIR) {
        () // Intentionally empty.
    }

    fn read_emp_line_1(&self) {
        () // Intentionally empty.
    }
}

static mut CHALLENGE_BACKEND: &dyn ChallengeBackend = &UnimplementedChallengeBackend;

pub fn set_challenge_backend(backend: &'static dyn ChallengeBackend) {
    unsafe {
        CHALLENGE_BACKEND = backend;
    }
}

pub fn set_boxed_challenge_backend(backend: Box<dyn ChallengeBackend>) {
    set_challenge_backend(Box::leak(backend));
}

pub fn challenge_backend() -> &'static dyn ChallengeBackend {
    unsafe { CHALLENGE_BACKEND }
}
