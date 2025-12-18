/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use crate::sieve::*;
use crate::value::*;
use crate::value_conversions::*;
use crate::context::*;
use crate::integer::*;
use crate::zksc_integer::ZkscIntDisplay;
use crate::zksc_types::*;
use crate::consts::*;
use crate::circuit_parser::*;
use crate::stack::*;

use std::borrow::{Borrow,BorrowMut};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::iter;
use log::debug;
use log::error;
use num_bigint::{BigInt,Sign};
use num_traits::{Zero,One};
use num_traits::cast::ToPrimitive;

const DEBUG : bool = cfg!(feature = "zksc_debug");

const PANIC_ON_ZKSC_ASSERT : bool = cfg!(feature = "panic_on_zksc_assert");

#[allow(non_camel_case_types)]
pub type unit = (); // used for easier code generation in generated.rs
// Should be false be default, can be set to true to skip making values unknown,
// so that assertions made on those values are not skipped. This can be much slower.
// Also make_not_unknown checks that the $pre and $post arguments have the equal value in this case.
const DEBUG_MAKE_UNKNOWN : bool = false;

fn use_iter_plugin(ctx: &ContextRef) -> bool {
    ctx.is_iter_available
}

fn eprint_traces(ctx: &ContextRef){
    eprint_stack("zksc stack backtrace:",&ctx.stack_trace);
    eprint_stack("zksc message trace",&ctx.message_stack);
}

/// Print stack trace and message trace to standard error.
fn eprint_stack(description: &str, stack : &RefCell<Vec<&'static str>>) {
    if stack.borrow().is_empty() {
        return;
    }

    error!("{}",description);
    for (i, m) in stack.borrow().iter().enumerate() {
        error!("{i: >4}: {m}");
    }
}

macro_rules! zksc_panic {
    ($ctx:ident, $($arg:tt)*) => {{
        eprint_traces($ctx);
        panic!{$($arg)*}
    }};
}

macro_rules! zksc_assert_panic {
    ($ctx:ident, $e:expr, $($arg:tt)*) => {{
        if ! $e {
            zksc_panic!($ctx, $($arg)*);
        }
    }}
}

macro_rules! zksc_assert_error {
    ($ctx:ident, $($arg:tt)*) => {{
        match $ctx {
            ctx => {
                if PANIC_ON_ZKSC_ASSERT {
                    zksc_panic!(ctx, $($arg)*);
                }

                if ctx.assert_error.borrow().is_none() {
                    eprint_traces(ctx);
                    error!($($arg)*);
                    let err = AssertError { reason: ctx.message_stack.borrow().clone() };
                    *ctx.assert_error.borrow_mut() = Some(err);
                }
            }
        }
    }};
}

#[allow(unused)]
#[inline]
pub fn with_loc(ctx: &ContextRef, loc: &'static str, func: impl FnOnce() -> Value) -> Value {
    if DEBUG {
        ctx.stack_trace.borrow_mut().push(loc);
        let result = func();
        ctx.stack_trace.borrow_mut().pop();
        result
    }
    else {
        func()
    }
}

#[allow(unused)]
#[inline]
pub fn with_loc_unit(ctx: &ContextRef, loc: &'static str, func: impl FnOnce()) {
    if DEBUG {
        ctx.stack_trace.borrow_mut().push(loc);
        let result = func();
        ctx.stack_trace.borrow_mut().pop();
        result
    }
    else {
        func()
    }
}

#[allow(unused)]
#[inline]
pub fn with_trace<T,F>(ctx: &ContextRef, msg: &'static str, func: F) -> T
    where F: FnOnce() -> T
{
    ctx.message_stack.borrow_mut().push(msg);
    let result = func();
    ctx.message_stack.borrow_mut().pop();
    result
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct QualifiedType {
    pub stage: StageType,
    pub domain: DomainType,
}

#[allow(unused)]
pub fn tcast(q: QualifiedType, d: DomainType) -> QualifiedType {
    QualifiedType{
        stage: tcast_stage(q.stage, d),
        domain: tcast_domain(q.domain, d),
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
#[allow(unused)]
pub enum TypeEnum {
    TEStage(StageType),
    TEDomain(DomainType),
    TENat(NatType),
    TEQualified(QualifiedType),
}
pub use TypeEnum::*;

#[allow(unused)]
pub fn get_testage(te: &TypeEnum) -> StageType {
    match te {
        TEStage(t) => t.clone(),
        _ => panic!("get_testage"),
    }
}

#[allow(unused)]
pub fn get_tedomain(te: &TypeEnum) -> DomainType {
    match te {
        TEDomain(t) => t.clone(),
        _ => panic!("get_tedomain"),
    }
}

#[allow(unused)]
pub fn get_tenat(te: &TypeEnum) -> &NatType {
    match te {
        TENat(t) => t,
        _ => panic!("get_tenat"),
    }
}

#[allow(unused)]
pub fn get_tequalified(te: &TypeEnum) -> QualifiedType {
    match te {
        TEQualified(t) => t.clone(),
        _ => panic!("get_tequalified"),
    }
}

fn is_nat_boolean(m: &NatType) -> bool {
    match m.modulus {
        Some(ref m) => m == &BigInt::from(2),
        _ => false,
    }
}

impl fmt::Display for NatType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.modulus {
            Some(ref x) => write!(f, "{}", x),
            _ => write!(f, "inf"),
        }
    }
}

pub type FnHOF = fn(&ContextRef, &mut Stack, &Vec<TypeEnum>, &Vec<Value>) -> Value;

// higher-order function
pub struct HOF {
    f: FnHOF,
    name: &'static str, // name of the function
    type_args: Vec<TypeEnum>, // the type arguments that have already been given
    value_args: Vec<Value>, // the value arguments that have already been given
    remaining_type_args: usize, // number of type arguments that still need to be given
    remaining_value_args: usize, // number of value arguments that still need to be given
    sieve_env_moduli: Vec<SoA<(NatType, bool)>>, // empty for non-SIEVE functions; the bool is true for $pre @public parameters
    is_sieve: bool, // can be true even if sieve_env_moduli is empty
}

impl fmt::Debug for HOF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HOF")
            .field("name", &self.name)
            .field("type_args", &self.type_args)
            .field("value_args", &self.value_args)
            .field("remaining_type_args", &self.remaining_type_args)
            .field("remaining_value_args", &self.remaining_value_args)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct Store {
    modulus: NatType,
    st: HashMap<Integer, Value>,
    pub def: bool,
}

#[allow(unused)]
#[inline(always)]
pub fn int_literal(ctx: &ContextRef, m: &NatType, index: usize) -> Value {
    let tag = m.tag as usize;
    let i = tag * ctx.integer_literal_count + index;
    ctx.integer_literal_cache[i].clone()
}

// Get value of uint[2^64] $pre @D for indexing
// Old version, used for range_array
#[inline(always)]
pub fn get_pre_index_old(x: &Value) -> isize {
    x.unwrap::<BigInt>().to_isize().expect("Index does not fit `isize`")
}

// Get value of uint[inf] $pre @D
#[inline(always)]
fn get_pre_uint_inf(x: &Value) -> &BigInt {
    x.unwrap::<BigInt>()
}

// Get value of uint[N] $S @D
pub fn get_pre_or_post_uint(m: &NatType, x: &Value) -> Integer {
    match x.view() {
        ValueView::ZkscDefined() => (m.to_bigint)(x),
        ValueView::Post(_, x) => get_pre_or_post_uint(m, x),
        _ => panic!("get_pre_or_post_uint: {:?}", x),
    }
}

// Get value of uint[N] $S @D or bool[N] $S @D as Integer
fn get_pre_or_post_uint_or_bool(ctx: &ContextRef, m: &NatType, x: &Value) -> Integer {
    match x.view() {
        ValueView::Bool(false) => ctx.integer_zero.clone(),
        ValueView::Bool(true) => ctx.integer_one.clone(),
        ValueView::ZkscDefined() => (m.to_bigint)(x),
        ValueView::Post(_, x) => get_pre_or_post_uint(m, x),
        ValueView::Unit() => ctx.integer_zero.clone(),
        _ => panic!("get_pre_or_post_uint: {:?}", x),
    }
}

pub fn get_vbool(x: &Value) -> &bool {
    match x.view() {
        ValueView::Bool(x) => x,
        ValueView::Post(_, x) => get_vbool(x),
        _ => panic!("get_vbool: {:?}", x),
    }
}

pub fn get_vstr(x: &Value) -> &str {
    match x.view() {
        ValueView::Str(x) => x.as_ref(),
        _ => panic!("get_vstr: {:?}", x),
    }
}

pub fn get_vstructvalue(x: &Value) -> &StructInner {
    match x.view() {
        ValueView::StructValue(x) => x,
        _ => panic!("get_vstructvalue: {:?}", x),
    }
}

pub fn get_varray(x: &Value) -> &Vec<Value> {
    match x.view() {
        ValueView::Array(x) => x,
        _ => panic!("get_varray: {:?}", x),
    }
}

pub fn get_varray_u8(x: &Value) -> &Vec<u8> {
    match x.view() {
        ValueView::ArrayU8(x) => x,
        _ => panic!("get_varray_u8: {:?}", x),
    }
}

pub fn get_varray_u16(x: &Value) -> &Vec<u16> {
    match x.view() {
        ValueView::ArrayU16(x) => x,
        _ => panic!("get_varray_u16: {:?}", x),
    }
}

pub fn get_varray_u32(x: &Value) -> &Vec<u32> {
    match x.view() {
        ValueView::ArrayU32(x) => x,
        _ => panic!("get_varray_u32: {:?}", x),
    }
}

pub fn get_varray_u64(x: &Value) -> &Vec<u64> {
    match x.view() {
        ValueView::ArrayU64(x) => x,
        _ => panic!("get_varray_u64: {:?}", x),
    }
}

pub fn get_varray_u128(x: &Value) -> &Vec<u128> {
    match x.view() {
        ValueView::ArrayU128(x) => x,
        _ => panic!("get_varray_u128: {:?}", x),
    }
}

pub fn get_varray_mut(x: &Value) -> &mut Vec<Value> {
    match x.view_mut() {
        ValueViewMut::Array(x) => x,
        // _ => panic!("get_varray_mut: {:?}", x),
        _ => panic!("get_varray_mut"),
    }
}

pub fn get_vpostsoa(x: &Value) -> &SoA<(WireRange, Vec<Value>)> {
    match x.view() {
        ValueView::PostSoA(x) => x,
        _ => panic!("get_vpostsoa: {:?}", x),
    }
}

pub fn get_vfun(x: &Value) -> &HOF {
    match x.view() {
        ValueView::FunValue(f) => f,
        _ => panic!("get_vfun: {:?}", x),
    }
}

pub fn get_vstore(x: &Value) -> &Store {
    match x.view() {
        ValueView::StoreValue(st) => st.borrow(),
        _ => panic!("get_vstore: {:?}", x),
    }
}

pub fn get_vstore_mut(x: &Value) -> &mut Store {
    match x.view_mut() {
        ValueViewMut::StoreValue(st) => st.borrow_mut(),
        _ => panic!("get_vstore_mut"),
    }
}

pub fn get_wire(x: &Value) -> &Wire {
    match x.view() {
        ValueView::Post(w, _) => w,
        ValueView::Unknown(_) => panic!("get_wire: Unknown"),
        _ => panic!("get_wire: {:?}", x),
    }
}

fn get_tuple_wires_helper<'a>(ctx: &ContextRef, moduli: &Vec<&NatType>, x: &'a Value, res: &mut Vec<WireOrConst<'a>>) {
    match x.view() {
        ValueView::Post(w, _) => res.push(WireOrConst::W(w)),
        ValueView::StructValue(tuple) => tuple.fields.iter().for_each(|x| get_tuple_wires_helper(ctx, moduli, x, res)),
        ValueView::Array(vs) => vs.iter().for_each(|x| get_tuple_wires_helper(ctx, moduli, x, res)),
        ValueView::Unit() => {},
        ValueView::Unknown(_) => panic!("get_tuple_wires: Unknown"),
        _ => res.push(WireOrConst::C(get_pre_or_post_uint_or_bool(ctx, moduli[res.len()], x))),
    }
}

fn get_tuple_wires<'a>(ctx: &'a ContextRef, moduli: &'a Vec<&NatType>, x: &'a Value) -> Vec<WireOrConst<'a>> {
    let mut res = Vec::new();
    get_tuple_wires_helper(ctx, moduli, x, &mut res);
    res
}

pub fn get_or_create_wire(m: &NatType, x: &Value) -> Wire {
    match x.view() {
        ValueView::Post(w, _) => sieve_backend().clone_wire(w),
        ValueView::Bool(b) => sieve_backend().const_bool(m, *b),
        ValueView::ZkscDefined() => sieve_backend().const_uint(m, x),
        ValueView::Unknown(_) => panic!("get_or_create_wire: Unknown"),
        _ => panic!("get_or_create_wire: {:?}", x),
    }
}

pub fn get_pre_value_from_post(x: &Value) -> &Value {
    match x.view() {
        ValueView::Post(_, v) => v,
        _ => x,
    }
}

pub fn is_unknown(x: &Value) -> bool {
    match x.view() {
        ValueView::Unknown(_) => true,
        ValueView::Post(_, x) => is_unknown(x),
        _ => false,
    }
}

pub fn is_part_of_unknown(x: &Value) -> bool {
    match x.view() {
        ValueView::PartOfUnknown() => true,
        _ => false,
    }
}

pub fn is_unknown_or_part_of_unknown(x: &Value) -> bool {
    match x.view() {
        ValueView::Unknown(_) => true,
        ValueView::Post(_, x) => is_unknown(x),
        ValueView::PartOfUnknown() => true,
        _ => false,
    }
}

pub fn get_part_of_unknown_mut<'a>(x: &'a mut Value) -> &'a mut Value {
    match x.view_mut() {
        ValueViewMut::Unknown(v) => v,
        _ => panic!("get_part_of_unknown_mut"),
    }
}

fn is_const_or_pre(x: &Value) -> bool {
    match x.view() {
        ValueView::ZkscDefined() => true,
        ValueView::Bool(_) => true,
        ValueView::Unknown(_) => true,
        _ => false,
    }
}

pub fn is_int_const_or_pre(x: &Value) -> bool {
    match x.view() {
        ValueView::ZkscDefined() => true,
        ValueView::Unknown(_) => true,
        _ => false,
    }
}

fn is_bool_const_or_pre(x: &Value) -> bool {
    match x.view() {
        ValueView::Bool(_) => true,
        _ => false,
    }
}

macro_rules! gen_sieve_ir1e {
    () => {
        pub fn sieve_and(_ctx: &ContextRef, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
            sieve_backend().and(m, w1, w2)
        }

        pub fn sieve_xor(_ctx: &ContextRef, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
            sieve_backend().xor(m, w1, w2)
        }

        pub fn sieve_not(_ctx: &ContextRef, m: &NatType, w1: &Wire) -> Wire {
            sieve_backend().not(m, w1)
        }

        pub fn sieve_copy_bool(_ctx: &ContextRef, m: &NatType, w: &Wire) -> Wire {
            sieve_backend().copy_bool(m, w)
        }

        pub fn sieve_const_bool(_ctx: &ContextRef, m: &NatType, c: bool) -> Wire {
            sieve_backend().const_bool(m, c)
        }

        pub fn sieve_mul(_ctx: &ContextRef, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
            sieve_backend().mul(m, w1, w2)
        }

        pub fn sieve_add(_ctx: &ContextRef, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
            sieve_backend().add(m, w1, w2)
        }

        pub fn sieve_mulc(_ctx: &ContextRef, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
            sieve_backend().mulc(m, w1, c2)
        }

        pub fn sieve_addc(_ctx: &ContextRef, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
            sieve_backend().addc(m, w1, c2)
        }

        pub fn sieve_assert_zero(_ctx: &ContextRef, m: &NatType, w: &Wire) {
            sieve_backend().assert_zero(m, w);
        }

        pub fn sieve_assert_eq(_ctx: &ContextRef, m1: &NatType, w1: &Wire, m2: &NatType, w2: &Wire) {
            sieve_backend().assert_eq(m1, w1, m2, w2);
        }

        pub fn sieve_assert_eq_scalar_vec(_ctx: &ContextRef, m: &NatType, w1: &Wire, m2: &NatType, wires: Vec<Wire>) {
            sieve_backend().assert_eq_scalar_vec(m, w1, m2, wires);
        }

        pub fn sieve_get_instance(_ctx: &ContextRef, m: &NatType) -> Wire {
            sieve_backend().get_instance(m)
        }

        pub fn sieve_get_witness(_ctx: &ContextRef, m: &NatType) -> Wire {
            let w = sieve_backend().get_witness(m);
            challenge_backend().read_witness_confirmation(sieve_backend());
            w
        }

        pub fn sieve_add_instance(_ctx: &ContextRef, m: &NatType, x: &Value) {
            sieve_backend().add_instance(m, x)
        }

        pub fn sieve_add_witness(_ctx: &ContextRef, m: &NatType, x: &Value) {
            sieve_backend().add_witness(m, x)
        }

        pub fn sieve_bool2int(_ctx: &ContextRef, m: &NatType, w : &Wire, output_modulus: &NatType) -> Wire {
            sieve_backend().bool2int(m, w, output_modulus)
        }

        pub fn sieve_int_field_switch(_ctx: &ContextRef, m : &NatType, w : &Wire, output_modulus: &NatType) -> Wire {
            sieve_backend().int_field_switch(m,w, output_modulus)
        }

        pub fn sieve_clone_wire(_ctx: &ContextRef, _m : &NatType, w : &Wire) -> Wire {
            sieve_backend().clone_wire(w)
        }

        pub fn sieve_challenge(_ctx: &ContextRef, m : &NatType, n: usize) -> Value {
            challenge_backend().challenge(sieve_backend(), m, n)
        }

        pub fn sieve_zero_wire(_ctx: &ContextRef, _m: &NatType) -> Wire {
            sieve_backend().zero_wire(_m)
        }
    };
}

#[allow(unused)]
macro_rules! gen_sieve_nop {
    () => {
        pub fn sieve_and(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_xor(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_not(_ctx: &ContextRef, _m: &NatType, _w1: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_copy_bool(_ctx: &ContextRef, _m: &NatType, _w: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_const_bool(_ctx: &ContextRef, _m: &NatType, _c: bool) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_mul(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_add(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _w2: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_mulc(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _c2: &Integer) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_addc(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _c2: &Integer) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_assert_zero(_ctx: &ContextRef, _m: &NatType, _w1: &Wire) { }
        pub fn sieve_assert_eq(_ctx: &ContextRef, _m1: &NatType, _w1: &Wire, _m2: &NatType, _w2: &Wire) { }
        pub fn sieve_assert_eq_scalar_vec(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _m2: &NatType, _wires: Vec<Wire>) { }
        pub fn sieve_get_instance(_ctx: &ContextRef, _m: &NatType) -> Wire { sieve_backend().zero_wire(_m) }
        pub fn sieve_get_witness(_ctx: &ContextRef, _m: &NatType) -> Wire { sieve_backend().zero_wire(_m) }
        pub fn sieve_add_instance(_ctx: &ContextRef, _m: &NatType, _x: &Value) { }
        pub fn sieve_add_witness(_ctx: &ContextRef, _m: &NatType, _x: &Value) { }
        pub fn sieve_clone_wire(_ctx: &ContextRef, _m: &NatType, _w1: &Wire) -> Wire {sieve_backend().zero_wire(_m)}
        pub fn sieve_bool2int(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _output_modulus: &NatType) -> Wire {sieve_backend().zero_wire(_output_modulus)}
        pub fn sieve_int_field_switch(_ctx: &ContextRef, _m: &NatType, _w1: &Wire, _output_modulus: &NatType) -> Wire {sieve_backend().zero_wire(_output_modulus)}
        pub fn sieve_challenge(_ctx : &ContextRef, m :&NatType, n: usize) -> Integer { challenge_backend().challenge(sieve_backend(), m, n) }
        pub fn sieve_zero_wire(_ctx: &ContextRef, _m: &NatType) -> Wire {sieve_backend().zero_wire(_m)}
    };
}

//gen_sieve_nop!(); // Useful for benchmarking only the public computation.
gen_sieve_ir1e!();

#[allow(unused)]
pub fn pred_field(ctx: &ContextRef, m: &NatType) -> bool {
    ctx.supported_fields.contains(&BigInt::from(m.tag))
}

#[allow(unused)]
pub fn pred_post_ring(ctx: &ContextRef, m: &NatType) -> bool {
    ctx.supported_fields.contains(&BigInt::from(m.tag))
}

#[allow(unused)]
pub fn pred_challenge(ctx: &ContextRef, m: &NatType) -> bool {
    ctx.supported_challenges.contains(&BigInt::from(m.tag))
}

#[allow(unused)]
pub fn pred_convertible(ctx: &ContextRef, m1: &NatType, m2: &NatType) -> bool {
    ctx.supported_conversions.contains(&(BigInt::from(m1.tag), BigInt::from(m2.tag)))
}

#[allow(unused)]
pub fn pred_post_convertible(ctx: &ContextRef, m1: &NatType, m2: &NatType) -> bool {
    ctx.supported_conversions.contains(&(BigInt::from(m1.tag), BigInt::from(m2.tag)))
}

#[allow(unused)]
pub fn plugin_supported(ctx: &ContextRef, plugin: &str) -> bool {
    ctx.supported_plugins.contains(plugin)
}

pub fn get_or_create_bool2_wire(ctx: &ContextRef, m: &NatType, x: &Value) -> Wire {
    match x.view() {
        ValueView::Post(w, _) => sieve_clone_wire(ctx,m,w),
        ValueView::Bool(b) => sieve_const_bool(ctx,m,*b),
        _ => zksc_panic!(ctx, "get_or_create_bool2_wire"),
    }
}

#[allow(unused)]
pub fn immutable_to_mutable(ctx: &ContextRef, x: &Value) -> Value {
    x.clone()
}

#[allow(unused)]
pub fn mutable_to_immutable(ctx: &ContextRef, x: &Value) -> Value {
    if is_part_of_unknown(x) {
        ctx.unknown.clone()
    } else {
        x.clone()
    }
}

// x := y, where x is mutable, y is immutable
#[allow(unused)]
pub fn assign_to_mutable(ctx: &ContextRef, x: &mut Value, y: &Value) {
    if !is_part_of_unknown(x) {
        x.assign(y);
    }
}

#[allow(unused)]
pub fn create_store(ctx: &ContextRef, m: &NatType, s: StageType, d: DomainType, assocs: &[(&Value, &Value)]) -> Value {
    match s {
        Pre => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                let st = assocs.iter().map(|(k,v)| (get_pre_or_post_uint(m, k), (*v).clone())).collect();
                rep::StoreValue::new(Box::new(Store { modulus: m.clone(), st, def: STORES_WITH_DEFAULT }))
            }
        }
        Post => panic!("Builtin $post stores are no longer supported"),
    }
}

// TODO: Un-necessary allocation
fn get_store_default_value(ctx: &ContextRef, m: &NatType) -> Value {
    (m.from_bigint)(&ctx.integer_zero)
}

fn get_value_with_default(ctx: &ContextRef, def: bool, m: &NatType, x: Option<&Value>) -> Value {
    if def {
        match x {
            None => get_store_default_value(ctx, m),
            Some(x) => x.clone(),
        }
    } else {
        x.expect("Key is not an element of store").clone()
    }
}

#[allow(unused)]
pub fn __set_store_default_unsafe(ctx: &ContextRef, _m: &NatType, _d: DomainType, st: &Value, def: bool) {
    if !is_unknown_or_part_of_unknown(st) {
        let st = get_vstore_mut(st);
        st.def = def;
    }
}

#[allow(unused)]
pub fn read_store(ctx: &ContextRef, st: &Value, k: &Value) -> Value {
    if is_unknown_or_part_of_unknown(st) || is_unknown_or_part_of_unknown(k) {
        ctx.unknown.clone()
    } else {
        let st = get_vstore(st);
        get_value_with_default(ctx, st.def, &st.modulus, st.st.get(&get_pre_or_post_uint(&st.modulus, k)))
    }
}

#[allow(unused)]
pub fn write_store(ctx: &ContextRef, st: &mut Value, k: &Value, v: &Value) {
    if is_unknown_or_part_of_unknown(st) {
    } else if is_unknown_or_part_of_unknown(k) {
        st.assign(&ctx.unknown);
    } else {
        st.make_shallow_copy_if_not_unique();
        let st = get_vstore_mut(st);
        st.st.insert(get_pre_or_post_uint(&st.modulus, k), v.clone());
    }
}

#[allow(unused)]
#[inline]
pub fn index_vector(ctx: &ContextRef, x: &Vec<Value>, i: u64) -> Value {
    x[i as usize].clone()
}

fn index_array_helper(ctx: &ContextRef, x: &Value, i: usize) -> Value {
    match x.view() {
        ValueView::Array(x) => x[i].clone(),
        ValueView::PostSoA(soa) => post_soa_index(soa, i),
        ValueView::Slice(v, ir) => index_array_helper(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => ctx.unknown.clone(),
        _ => panic!("index_array: not an array or list"),
    }
}

#[inline]
fn index_array_polymorphic_helper(ctx: &ContextRef, d: DomainType, x: &Value, i: usize) -> Value {
    match x.view() {
        ValueView::Array(x) => x[i].clone(),
        ValueView::ArrayU8(x) => u8_to_value(ctx, d, x[i]),
        ValueView::ArrayU16(x) => u16_to_value(ctx, d, x[i]),
        ValueView::ArrayU32(x) => u32_to_value(ctx, d, x[i]),
        ValueView::ArrayU64(x) => u64_to_value(ctx, d, x[i]),
        ValueView::ArrayU128(x) => u128_to_value(ctx, d, x[i]),
        ValueView::ArrayBool(x) => bool_to_value(ctx, d, x[i]),
        ValueView::ArrayUnit(len) => { assert!(i < *len, "index out of bounds"); ctx.scalar.clone() },
        ValueView::PostSoA(soa) => post_soa_index(soa, i),
        ValueView::Slice(v, ir) => index_array_helper(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => ctx.unknown.clone(),
        _ => panic!("index_array: not an array or list"),
    }
}

#[inline]
fn index_array_helper_u8(ctx: &ContextRef, x: &Value, i: usize) -> u8 {
    match x.view() {
        ValueView::Array(x) => value_to_u8(&x[i]),
        ValueView::ArrayU8(x) => x[i],
        ValueView::Slice(v, ir) => index_array_helper_u8(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => 0,
        _ => panic!("index_array_u8: not a u8 array or list"),
    }
}

#[inline]
fn index_array_helper_u16(ctx: &ContextRef, x: &Value, i: usize) -> u16 {
    match x.view() {
        ValueView::Array(x) => value_to_u16(&x[i]),
        ValueView::ArrayU16(x) => x[i],
        ValueView::Slice(v, ir) => index_array_helper_u16(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => 0,
        _ => panic!("index_array_u16: not a u16 array or list"),
    }
}

#[inline]
fn index_array_helper_u32(ctx: &ContextRef, x: &Value, i: usize) -> u32 {
    match x.view() {
        ValueView::Array(x) => value_to_u32(&x[i]),
        ValueView::ArrayU32(x) => x[i],
        ValueView::Slice(v, ir) => index_array_helper_u32(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => 0,
        _ => panic!("index_array_u32: not a u32 array or list"),
    }
}

#[inline]
fn index_array_helper_u64(ctx: &ContextRef, x: &Value, i: usize) -> u64 {
    match x.view() {
        ValueView::Array(x) => value_to_u64(&x[i]),
        ValueView::ArrayU64(x) => x[i],
        ValueView::Slice(v, ir) => index_array_helper_u64(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => 0,
        _ => panic!("index_array_u64: not a u64 array or list"),
    }
}

#[inline]
fn index_array_helper_u128(ctx: &ContextRef, x: &Value, i: usize) -> u128 {
    match x.view() {
        ValueView::Array(x) => value_to_u128(&x[i]),
        ValueView::ArrayU128(x) => x[i],
        ValueView::Slice(v, ir) => index_array_helper_u128(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => 0,
        _ => panic!("index_array_u128: not a u128 array or list"),
    }
}

#[inline]
fn index_array_helper_bool(ctx: &ContextRef, x: &Value, i: usize) -> bool {
    match x.view() {
        ValueView::Array(x) => value_to_bool(&x[i]),
        ValueView::ArrayBool(x) => x[i],
        ValueView::Slice(v, ir) => index_array_helper_bool(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => false,
        _ => panic!("index_array_bool: not an bool array or list"),
    }
}

#[inline]
fn index_array_helper_unit(ctx: &ContextRef, x: &Value, i: usize) -> () {
    match x.view() {
        ValueView::Array(x) => value_to_unit(&x[i]),
        ValueView::ArrayUnit(len) => assert!(i < *len, "index out of bounds"),
        ValueView::Slice(v, ir) => index_array_helper_unit(ctx, v, ir.index(i)),
        ValueView::Unknown(_) => (),
        _ => panic!("index_array_unit: not an unit array or list"),
    }
}

#[allow(unused)]
#[inline]
pub fn index_array(ctx: &ContextRef, x: &Value, i: u64) -> Value {
    index_array_helper(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_polymorphic(ctx: &ContextRef, d: DomainType, x: &Value, i: u64) -> Value {
    index_array_polymorphic_helper(ctx, d, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_u8(ctx: &ContextRef, x: &Value, i: u64) -> u8 {
    index_array_helper_u8(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_u16(ctx: &ContextRef, x: &Value, i: u64) -> u16 {
    index_array_helper_u16(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_u32(ctx: &ContextRef, x: &Value, i: u64) -> u32 {
    index_array_helper_u32(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_u64(ctx: &ContextRef, x: &Value, i: u64) -> u64 {
    index_array_helper_u64(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_u128(ctx: &ContextRef, x: &Value, i: u64) -> u128 {
    index_array_helper_u128(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_bool(ctx: &ContextRef, x: &Value, i: u64) -> bool {
    index_array_helper_bool(ctx, x, i as usize)
}

#[allow(unused)]
#[inline]
pub fn index_array_unit(ctx: &ContextRef, x: &Value, i: u64) -> () {
    index_array_helper_unit(ctx, x, i as usize)
}

#[allow(unused)]
pub fn index_tensor(ctx: &ContextRef, s: StageType, d: DomainType, dl: DomainType, v: &Value, indices: &Value) -> Value {
    if dl > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let indices: Vec<usize> =
            match indices.view() {
                ValueView::ArrayU64(indices) => {
                    indices.iter().map(|v| *v as usize).collect()
                }
                ValueView::Array(indices) => {
                    indices.iter().map(|v| value_to_u64(v) as usize).collect()
                }
                _ => panic!("index_tensor: indices are not a list"),
            };
        match v.view() {
            ValueView::Tensor(arr, dim) => {
                let mut index: usize = 0;
                assert!(indices.len() == dim.len(), "index_tensor: number of indices does not match dimension");
                for i in 0 .. dim.len() {
                    assert!(indices[i] < dim[i], "index_tensor: index out of bounds");
                    index = index * dim[i] + indices[i];
                }
                index_array_helper(ctx, arr, index)
            }
            _ => {
                assert!(indices.len() == 1, "index_tensor: number of indices does not match dimension");
                index_array_helper(ctx, v, indices[0])
            }
        }
    }
}

#[allow(unused)]
pub fn index_tensor_1(ctx: &ContextRef, s: StageType, d: DomainType, dl: DomainType, v: &Value, index: u64) -> Value {
    if dl > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let index = index as usize;
        match v.view() {
            ValueView::Tensor(arr, dim) => {
                assert!(dim.len() >= 2, "index_tensor_1 can only be used with tensors with dimension at least 2");
                assert!(index < dim[0], "index_tensor_1: index out of bounds");
                let n = length_helper(arr);
                let n1 = n / dim[0];
                let i1 = n1 * index;
                let i2 = n1 * (index + 1);
                let slice = slice_array_helper(ctx, arr, i1, i2);
                if dim.len() == 2 {
                    slice
                } else {
                    let dim_new = dim[1..].to_vec();
                    rep::Tensor::new(slice, dim_new)
                }
            }
            _ => panic!("index_tensor_1 can only be used with tensors with dimension at least 2"),
        }
    }
}

#[inline]
fn slice_array_helper(ctx: &ContextRef, x: &Value, i1: usize, i2: usize) -> Value {
    if is_unknown_or_part_of_unknown(x) {
        ctx.unknown.clone()
    } else {
        assert!(i1 <= i2);
        let len = i2 - i1;
        match x.view() {
            ValueView::Array(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayU8(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayU16(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayU32(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayU64(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayU128(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayBool(arr) => {
                assert!(i2 <= arr.len());
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::ArrayUnit(len0) => {
                assert!(i2 <= *len0);
                rep::ArrayUnit::new(len)
            }
            ValueView::PostSoA(soa) => {
                assert!(i2 <= post_soa_length(soa));
                rep::Slice::new(x.clone(), IndexRange { first: i1, length: len })
            }
            ValueView::Slice(v, ir) => {
                assert!(i2 <= ir.length);
                rep::Slice::new(v.clone(), IndexRange { first: ir.first + i1, length: len })
            }
            ValueView::Tensor(arr, dim) => {
                let n = length_helper(arr);
                let n1 = n / dim[0];
                let i1 = n1 * i1;
                let i2 = n1 * i2;
                let slice = slice_array_helper(ctx, arr, i1, i2);
                let mut dim_new = dim.clone();
                dim_new[0] = len;
                rep::Tensor::new(slice, dim_new)
            }
            _ => panic!("slice_array: not an array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn slice_array(ctx: &ContextRef, x: &Value, i1: u64, i2: u64) -> Value {
    let i1 = i1 as usize;
    let i2 = i2 as usize;
    slice_array_helper(ctx, x, i1, i2)
}

#[allow(unused)]
#[inline]
pub fn slice_array_to(ctx: &ContextRef, x: &Value, i2: u64) -> Value {
    let i2 = i2 as usize;
    slice_array_helper(ctx, x, 0, i2)
}

#[allow(unused)]
#[inline]
pub fn slice_array_from(ctx: &ContextRef, x: &Value, i1: u64) -> Value {
    let i1 = i1 as usize;
    slice_array_helper(ctx, x, i1, length_helper(x))
}

#[allow(unused)]
#[inline]
pub fn index_array_assign(ctx: &ContextRef, x: &mut Value, i: u64, y: &Value) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(y),
            ValueViewMut::ArrayU8(x) => x[i as usize] = value_to_u8(y),
            ValueViewMut::ArrayU16(x) => x[i as usize] = value_to_u16(y),
            ValueViewMut::ArrayU32(x) => x[i as usize] = value_to_u32(y),
            ValueViewMut::ArrayU64(x) => x[i as usize] = value_to_u64(y),
            ValueViewMut::ArrayU128(x) => x[i as usize] = value_to_u128(y),
            ValueViewMut::ArrayBool(x) => x[i as usize] = value_to_bool(y),
            _ => panic!("index_array_assign"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_u8(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: u8) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(&u8_to_value(ctx, d, y)),
            ValueViewMut::ArrayU8(x) => x[i as usize] = y,
            _ => panic!("index_array_assign_u8: not a u8 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_u16(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: u16) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(&u16_to_value(ctx, d, y)),
            ValueViewMut::ArrayU16(x) => x[i as usize] = y,
            _ => panic!("index_array_assign_u16: not a u16 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_u32(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: u32) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(&u32_to_value(ctx, d, y)),
            ValueViewMut::ArrayU32(x) => x[i as usize] = y,
            _ => panic!("index_array_assign_u32: not a u32 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_u64(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: u64) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(&u64_to_value(ctx, d, y)),
            ValueViewMut::ArrayU64(x) => x[i as usize] = y,
            _ => panic!("index_array_assign_u64: not a u64 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_u128(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: u128) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(&u128_to_value(ctx, d, y)),
            ValueViewMut::ArrayU128(x) => x[i as usize] = y,
            _ => panic!("index_array_assign_u128: not a u128 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_bool(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: bool) {
    if !is_unknown_or_part_of_unknown(x) {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(x) => x.get_mut(i as usize).expect("Index out of bounds").assign(&bool_to_value(ctx, d, y)),
            ValueViewMut::ArrayBool(x) => x[i as usize] = y,
            _ => panic!("index_array_assign_bool: not a bool array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_assign_unit(ctx: &ContextRef, d: DomainType, x: &mut Value, i: u64, y: ()) {
    if !is_unknown_or_part_of_unknown(x) {
        match x.view_mut() {
            ValueViewMut::Array(x) => assert!((i as usize) < x.len(), "Index out of bounds"),
            ValueViewMut::ArrayUnit(len) => assert!((i as usize) < *len, "Index out of bounds"),
            _ => panic!("index_array_assign_unit: not a unit array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut Value {
    if is_part_of_unknown(x) {
        x
    } else if is_unknown(x) {
        get_part_of_unknown_mut(x)
    } else {
        x.make_shallow_copy_if_not_unique();
        get_varray_mut(x).get_mut(i as usize).expect("Index out of bounds")
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut_u8<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut u8 {
    if is_unknown_or_part_of_unknown(x) {
        panic!("Elements of unboxed arrays of higher domain than the current context are not supported as ref arguments.")
    } else {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU8(x) => x.get_mut(i as usize).expect("Index out of bounds"),
            ValueViewMut::Array(_) => panic!("Primitive elements of boxed arrays are not supported as ref arguments."),
            _ => panic!("index_array_mut_u8: not a u8 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut_u16<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut u16 {
    if is_unknown_or_part_of_unknown(x) {
        panic!("Elements of unboxed arrays of higher domain than the current context are not supported as ref arguments.")
    } else {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU16(x) => x.get_mut(i as usize).expect("Index out of bounds"),
            ValueViewMut::Array(_) => panic!("Primitive elements of boxed arrays are not supported as ref arguments."),
            _ => panic!("index_array_mut_u16: not a u16 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut_u32<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut u32 {
    if is_unknown_or_part_of_unknown(x) {
        panic!("Elements of unboxed arrays of higher domain than the current context are not supported as ref arguments.")
    } else {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU32(x) => x.get_mut(i as usize).expect("Index out of bounds"),
            ValueViewMut::Array(_) => panic!("Primitive elements of boxed arrays are not supported as ref arguments."),
            _ => panic!("index_array_mut_u32: not a u32 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut_u64<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut u64 {
    if is_unknown_or_part_of_unknown(x) {
        panic!("Elements of unboxed arrays of higher domain than the current context are not supported as ref arguments.")
    } else {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU64(x) => x.get_mut(i as usize).expect("Index out of bounds"),
            ValueViewMut::Array(_) => panic!("Primitive elements of boxed arrays are not supported as ref arguments."),
            _ => panic!("index_array_mut_u64: not a u64 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut_u128<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut u128 {
    if is_unknown_or_part_of_unknown(x) {
        panic!("Elements of unboxed arrays of higher domain than the current context are not supported as ref arguments.")
    } else {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU128(x) => x.get_mut(i as usize).expect("Index out of bounds"),
            ValueViewMut::Array(_) => panic!("Primitive elements of boxed arrays are not supported as ref arguments."),
            _ => panic!("index_array_mut_u128: not a u128 array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_array_mut_bool<'a>(ctx: &ContextRef, x: &'a mut Value, i: u64) -> &'a mut bool {
    if is_unknown_or_part_of_unknown(x) {
        panic!("Elements of unboxed arrays of higher domain than the current context are not supported as ref arguments.")
    } else {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayBool(x) => x.get_mut(i as usize).expect("Index out of bounds"),
            ValueViewMut::Array(_) => panic!("Primitive elements of boxed arrays are not supported as ref arguments."),
            _ => panic!("index_array_mut_bool: not a bool array or list"),
        }
    }
}

#[allow(unused)]
#[inline]
pub fn index_struct(ctx: &ContextRef, x: &Value, i: usize) -> Value {
    if is_unknown_or_part_of_unknown(x) {
        x.clone()
    } else {
        let fields = &x.unwrap::<rep::StructValue>().0.fields;
        fields[i].clone()
    }
}

#[allow(unused)]
#[inline]
pub fn index_struct_mut<'a>(ctx: &ContextRef, x: &'a mut Value, i: usize) -> &'a mut Value {
    if is_part_of_unknown(x) {
        x
    } else if is_unknown(x) {
        get_part_of_unknown_mut(x)
    } else {
        x.make_shallow_copy_if_not_unique();
        let fields = &mut x.unwrap_mut::<rep::StructValue>().0.fields;
        &mut fields[i]
    }
}

#[allow(unused)]
#[inline]
pub fn create_array(ctx: &ContextRef, d: DomainType, xs: Vec<Value>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::Array::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_u8(ctx: &ContextRef, d: DomainType, xs: Vec<u8>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayU8::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_u16(ctx: &ContextRef, d: DomainType, xs: Vec<u16>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayU16::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_u32(ctx: &ContextRef, d: DomainType, xs: Vec<u32>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayU32::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_u64(ctx: &ContextRef, d: DomainType, xs: Vec<u64>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayU64::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_u128(ctx: &ContextRef, d: DomainType, xs: Vec<u128>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayU128::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_bool(ctx: &ContextRef, d: DomainType, xs: Vec<bool>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayBool::new(xs)
    }
}

#[allow(unused)]
#[inline]
pub fn create_array_unit(ctx: &ContextRef, d: DomainType, xs: Vec<()>) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        rep::ArrayUnit::new(xs.len())
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array(ctx: &ContextRef, d: DomainType, x: &Value, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).cloned().collect();
        rep::Array::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_u8(ctx: &ContextRef, d: DomainType, x: u8, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).collect();
        rep::ArrayU8::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_u16(ctx: &ContextRef, d: DomainType, x: u16, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).collect();
        rep::ArrayU16::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_u32(ctx: &ContextRef, d: DomainType, x: u32, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).collect();
        rep::ArrayU32::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_u64(ctx: &ContextRef, d: DomainType, x: u64, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).collect();
        rep::ArrayU64::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_u128(ctx: &ContextRef, d: DomainType, x: u128, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).collect();
        rep::ArrayU128::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_bool(ctx: &ContextRef, d: DomainType, x: bool, n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        let xs = iter::repeat(x).take(n).collect();
        rep::ArrayBool::new(xs)
    }
}

// [x; n]
#[allow(unused)]
pub fn replicated_array_unit(ctx: &ContextRef, d: DomainType, x: (), n: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n = n as usize;
        rep::ArrayUnit::new(n)
    }
}

// [x .. y]
#[allow(unused)]
pub fn range_array(ctx: &ContextRef, d: DomainType, x: &Value, y: &Value) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let n1 = get_pre_index_old(x);
        let n2 = get_pre_index_old(y);
        let xs = (n1 .. n2).map(|i| Value::new::<BigInt>(BigInt::from(i))).collect();
        rep::Array::new(xs)
    }
}

// [x .. y]
#[allow(unused)]
pub fn range_array_u8(ctx: &ContextRef, d: DomainType, x: u8, y: u8) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let xs = (x .. y).collect();
        rep::ArrayU8::new(xs)
    }
}

// [x .. y]
#[allow(unused)]
pub fn range_array_u16(ctx: &ContextRef, d: DomainType, x: u16, y: u16) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let xs = (x .. y).collect();
        rep::ArrayU16::new(xs)
    }
}

// [x .. y]
#[allow(unused)]
pub fn range_array_u32(ctx: &ContextRef, d: DomainType, x: u32, y: u32) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let xs = (x .. y).collect();
        rep::ArrayU32::new(xs)
    }
}

// [x .. y]
#[allow(unused)]
pub fn range_array_u64(ctx: &ContextRef, d: DomainType, x: u64, y: u64) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let xs = (x .. y).collect();
        rep::ArrayU64::new(xs)
    }
}

// [x .. y]
#[allow(unused)]
pub fn range_array_u128(ctx: &ContextRef, d: DomainType, x: u128, y: u128) -> Value {
    if d > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let xs = (x .. y).collect();
        rep::ArrayU128::new(xs)
    }
}

#[inline]
fn length_helper(x: &Value) -> usize {
    match x.view() {
        ValueView::Array(x) => x.len(),
        ValueView::ArrayU8(x) => x.len(),
        ValueView::ArrayU16(x) => x.len(),
        ValueView::ArrayU32(x) => x.len(),
        ValueView::ArrayU64(x) => x.len(),
        ValueView::ArrayU128(x) => x.len(),
        ValueView::ArrayBool(x) => x.len(),
        ValueView::ArrayUnit(len) => *len,
        ValueView::PostSoA(soa) => post_soa_length(soa),
        ValueView::Slice(_, ir) => ir.length,
        ValueView::Tensor(_, dim) => dim[0],
        _ => panic!("length: not an array or list"),
    }
}

#[allow(unused)]
pub fn length(
    ctx: &ContextRef,
    _s_elem: StageType,
    _d_elem: DomainType,
    d_length: DomainType,
    x: &Value,
) -> u64 {
    if d_length > CURR_DOMAIN && is_unknown(x) {
        0
    } else {
        length_helper(x) as u64
    }
}

fn make_unknown_helper(ctx: &ContextRef, x: &Value) -> Value {
    match x.view() {
        ValueView::Post(w, _) => rep::Post::new(w.clone(), ctx.unknown.clone()),
        ValueView::Array(xs) => rep::Array::new(xs.iter().map(|x| make_unknown_helper(ctx, x)).collect()),
        ValueView::PostSoA(soa) => rep::PostSoA::new(soa.map_ref(&|(wr, xs)| (wr.clone(), xs.iter().map(|_| ctx.unknown.clone()).collect()))),
        ValueView::Slice(_, _) => make_unknown_helper(ctx, &unslice_helper(x)),
        ValueView::Tensor(v, dim) => rep::Tensor::new(make_unknown_helper(ctx, v), dim.clone()),
        ValueView::StructValue(s) => rep::StructValue::new(StructInner {
            fields: s.fields.iter().map(|x| make_unknown_helper(ctx, x)).collect(),
            finalizer: s.finalizer.clone(),
        }),
        _ => x.clone(),
    }
}

#[allow(unused)]
pub fn make_unknown(
    ctx: &ContextRef,
    s: StageType,
    d: DomainType,
    x: &Value,
) -> Value {
    if DEBUG_MAKE_UNKNOWN {
        x.clone()
    } else {
        make_unknown_helper(ctx, x)
    }
}

#[allow(unused)]
pub fn make_not_unknown(
    ctx: &ContextRef,
    _m: &NatType,
    _d: DomainType,
    x_post: &Value,
    x_pre: &Value,
) -> Value {
    match x_post.view() {
        ValueView::Post(w, x) => {
            if DEBUG_MAKE_UNKNOWN {
                dbg_assert_eq(ctx, _d, _m, x, x_pre, "", "make_not_unknown");
            } else {
                assert!(is_unknown(x));
            }
            rep::Post::new(w.clone(), x_pre.clone())
        }
        _ => panic!("make_not_unknown: invalid argument type"),
    }
}

pub fn get_int(x : &Value) -> &Value {
    match x.view() {
        ValueView::ZkscDefined() => x,
        ValueView::Post(_,v) => v,
        _ => panic!("get_int cast on non-integral type: {:?}", x)
    }
}

#[allow(unused)]
pub fn cast_to_pre(x: &Value) -> &Value {
    match x.view() {
        ValueView::Post(_, x) => &x,
        _ => x,
    }
}

#[allow(unused)]
pub fn cast_to_domain(ctx: &ContextRef, d: DomainType, x: &Value) -> Value {
    match x.view() {
        ValueView::Array(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayU8(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayU16(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayU32(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayU64(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayU128(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayBool(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::ArrayUnit(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::Slice(_, _) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        ValueView::StoreValue(_) => {
            if d > CURR_DOMAIN {
                ctx.unknown.clone()
            } else {
                x.clone()
            }
        }
        _ => x.clone(),
    }
}

fn bool_to_uint(b: bool) -> Integer {
    if b {Integer::one()} else {Integer::zero()}
}

#[allow(unused)]
pub fn cast_to_bool(ctx : &ContextRef, input_modulus: &NatType, x: &Value, output_modulus: &NatType) -> Value {
    match x.view() {
        ValueView::Unknown(_) => x.clone(),
        ValueView::Bool(b) => x.clone(),
        ValueView::Post(w, v) => rep::Post::new(sieve_int_field_switch(ctx,input_modulus,w, output_modulus), v.clone()),
        _ => zksc_panic!(ctx, "cast_to_bool"),
    }
}

#[allow(unused)]
pub fn cast_to_uint(ctx : &ContextRef, stage: StageType, input_modulus: &NatType, x: &Value, output_modulus: &NatType) -> Value {
    match x.view() {
        ValueView::Unknown(_) => x.clone(),
        ValueView::ZkscDefined() => {
            if stage == Post && ctx.inside_sieve_fn_call() && sieve_backend().ring_switch_thru_assert_eq(input_modulus, output_modulus) {
                let res_pre = (output_modulus.from_bigint)(&(input_modulus.to_bigint)(x));
                let res_post = wire_uint(ctx, output_modulus, Prover, &res_pre); // TODO: this is inefficient for non-Prover
                res_post
            } else {
                (output_modulus.from_bigint)(&(input_modulus.to_bigint)(x))
            }
        },
        ValueView::Bool(b) => (output_modulus.from_bigint)(&bool_to_uint(*b)),
        ValueView::Post(w, v) => match v.view() {
            ValueView::Bool(_) => rep::Post::new(sieve_bool2int(ctx,input_modulus,w,output_modulus),cast_to_uint(ctx,Pre,input_modulus,v,output_modulus)),
            ValueView::ZkscDefined() => {
                if sieve_backend().ring_switch_thru_assert_eq(input_modulus, output_modulus) {
                    let res_pre = cast_to_uint(ctx,Pre,input_modulus,v,output_modulus);
                    let res_post = wire_uint(ctx, output_modulus, Prover, &res_pre); // TODO: this is inefficient for non-Prover
                    sieve_assert_eq(ctx, input_modulus, w, output_modulus, get_wire(&res_post));
                    res_post
                } else {
                    rep::Post::new(sieve_int_field_switch(ctx,input_modulus,w, output_modulus),cast_to_uint(ctx,Pre,input_modulus,v,output_modulus))
                }
            }
            ValueView::Unknown(_) => {
                if sieve_backend().ring_switch_thru_assert_eq(input_modulus, output_modulus) {
                    let res_pre = ctx.unknown.clone();
                    let res_post = wire_uint(ctx, output_modulus, Prover, &res_pre); // TODO: this is inefficient for non-Prover
                    sieve_assert_eq(ctx, input_modulus, w, output_modulus, get_wire(&res_post));
                    res_post
                } else {
                    rep::Post::new(sieve_int_field_switch(ctx,input_modulus,w, output_modulus), ctx.unknown.clone())
                }
            }
            _ => zksc_panic!(ctx, "cast_to_uint {:?}",x)
        }
        _ => zksc_panic!(ctx, "cast_to_uint"),
    }
}

#[allow(unused)]
#[inline(always)]
pub fn type_to_expr(m: &NatType) -> Value {
    match m.modulus {
        Some(_) => (m.modulus_value)(),
        None => panic!("Converting infinite natural to integer value."),
    }
}


// needed for vectorized applications
#[allow(unused)]
pub fn mul_moduli<'a>(_ctx: &'a ContextRef, m: &'a NatType, _s: StageType, _d: DomainType) -> (SoA<&'a NatType>, Vec<SoA<&'a NatType>>) {
    (SoA::Scalar(m), vec![SoA::Scalar(m), SoA::Scalar(m)])
}

// needed for vectorized applications
#[allow(unused)]
pub fn mul_hof(ctx: &ContextRef, _stack: &mut Stack, ts: &Vec<TypeEnum>, vs: &Vec<Value>) -> Value {
    mul(ctx, get_tenat(&ts[0]), get_testage(&ts[1]), get_tedomain(&ts[2]), &vs[0], &vs[1])
}

// needed for vectorized applications
#[allow(unused)]
pub fn add_moduli<'a>(_ctx: &'a ContextRef, m: &'a NatType, _s: StageType, _d: DomainType) -> (SoA<&'a NatType>, Vec<SoA<&'a NatType>>) {
    (SoA::Scalar(m), vec![SoA::Scalar(m), SoA::Scalar(m)])
}

// needed for vectorized applications
#[allow(unused)]
pub fn add_hof(ctx: &ContextRef, _stack: &mut Stack, ts: &Vec<TypeEnum>, vs: &Vec<Value>) -> Value {
    add(ctx, get_tenat(&ts[0]), get_testage(&ts[1]), get_tedomain(&ts[2]), &vs[0], &vs[1])
}

// needed for vectorized applications
#[allow(unused)]
pub fn sub_moduli<'a>(_ctx: &'a ContextRef, m: &'a NatType, _s: StageType, _d: DomainType) -> (SoA<&'a NatType>, Vec<SoA<&'a NatType>>) {
    (SoA::Scalar(m), vec![SoA::Scalar(m), SoA::Scalar(m)])
}

// needed for vectorized applications
#[allow(unused)]
pub fn sub_hof(ctx: &ContextRef, _stack: &mut Stack, ts: &Vec<TypeEnum>, vs: &Vec<Value>) -> Value {
    sub(ctx, get_tenat(&ts[0]), get_testage(&ts[1]), get_tedomain(&ts[2]), &vs[0], &vs[1])
}

// needed for vectorized applications
#[allow(unused)]
pub fn assert_zero_moduli<'a>(_ctx: &'a ContextRef, _d: DomainType, m: &'a NatType) -> (SoA<&'a NatType>, Vec<SoA<&'a NatType>>) {
    (SoA::Tuple(vec![]), vec![SoA::Scalar(m)])
}

// needed for vectorized applications
#[allow(unused)]
pub fn assert_zero_hof(ctx: &ContextRef, _stack: &mut Stack, ts: &Vec<TypeEnum>, vs: &Vec<Value>) -> Value {
    assert_zero(ctx, get_tedomain(&ts[0]), get_tenat(&ts[1]), &vs[0]);
    ctx.scalar.clone()
}


#[allow(unused)]
pub fn mul(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
    y0: &Value,
) -> Value {
    let r = if is_unknown(x0) || is_unknown(y0) {
        ctx.unknown.clone()
    } else {
        (m.mul)(get_int(x0),get_int(y0))
    };
    if NEED_REL && s == Post {
        let c1 = is_int_const_or_pre(x0);
        let c2 = is_int_const_or_pre(y0);
        match (c1, c2) {
            (false, false) => {
                let w1 = get_wire(x0);
                let w2 = get_wire(y0);
                let w = sieve_mul(ctx, &m, w1, w2);
                rep::Post::new(w, r)
            }
            (false, _) => {
                let w1 = get_wire(x0);
                let y = (m.to_bigint)(y0);
                let w = sieve_mulc(ctx, &m,  w1, &y);
                rep::Post::new(w, r)
            }
            (_, false) => {
                let w2 = get_wire(y0);
                let x = (m.to_bigint)(x0);
                let w = sieve_mulc(ctx, &m, w2, &x);
                rep::Post::new(w, r)
            }
            _ => r,
        }
    } else {
        r
    }
}

#[allow(unused)]
pub fn add(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
    y0: &Value,
) -> Value {
    let r = if is_unknown(x0) || is_unknown(y0) {
        ctx.unknown.clone()
    } else {
        (m.add)(get_int(x0),get_int(y0))
    };
    if NEED_REL && s == Post {
        let c1 = is_int_const_or_pre(x0);
        let c2 = is_int_const_or_pre(y0);
        match (c1, c2) {
            (false, false) => {
                let w1 = get_wire(x0);
                let w2 = get_wire(y0);
                let w = sieve_add(ctx, &m, w1, w2);
                rep::Post::new(w, r)
            }
            (false, _) => {
                let w1 = get_wire(x0);
                let y = (m.to_bigint)(y0);
                let w = sieve_addc(ctx, &m, w1, &y);
                rep::Post::new(w, r)
            }
            (_, false) => {
                let w2 = get_wire(y0);
                let x = (m.to_bigint)(x0);
                let w = sieve_addc(ctx, &m, w2, &x);
                rep::Post::new(w, r)
            }
            _ => r,
        }
    } else {
        r
    }
}

#[allow(unused)]
pub fn sub(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
    y0: &Value,
) -> Value {
    if m.ring_type == RingBitwise {
        return add(ctx, m, s, d, x0, y0);
    }
    let r = if is_unknown(x0) || is_unknown(y0) {
        ctx.unknown.clone()
    } else {
        (m.sub)(get_int(x0),get_int(y0))
    };
    if NEED_REL && s == Post {
        let c1 = is_int_const_or_pre(x0);
        let c2 = is_int_const_or_pre(y0);
        let m_orig = m;
        let modulus = match m.modulus {
            Some(ref m) => m,
            _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
        };
        match (c1, c2) {
            (false, false) => {
                let w1 = get_wire(x0);
                let w2 = get_wire(y0);
                let w = sieve_backend().sub(&m_orig, w1, w2);
                rep::Post::new(w, r)
            }
            (false, _) => {
                let w1 = get_wire(x0);
                let y = (m.to_bigint)(y0);
                let y_neg = (modulus - y) % modulus;
                let w = sieve_addc(ctx, &m_orig, w1, &y_neg);
                rep::Post::new(w, r)
            }
            (_, false) => {
                let w2 = get_wire(y0);
                let x = (m.to_bigint)(x0);
                let w = sieve_backend().subc(&m_orig, &x, w2);
                rep::Post::new(w, r)
            }
            _ => r,
        }
    } else {
        r
    }
}

#[allow(unused)]
pub fn and(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
    y0: &Value,
) -> Value {
    let r = if is_unknown(x0) || is_unknown(y0) {
        ctx.unknown.clone()
    } else {
        let x = *get_vbool(x0);
        let y = *get_vbool(y0);
        let z = x && y;
        rep::Bool::new(z)
    };
    if NEED_REL && s == Post {
        let c1 = is_bool_const_or_pre(x0);
        let c2 = is_bool_const_or_pre(y0);
        let f0 = || rep::Bool::new(false);
        let f1 = |x : &Value| x.clone();
        match (c1, c2) {
            (false, false) => {
                let w1 = get_wire(x0);
                let w2 = get_wire(y0);
                let w = if is_nat_boolean(m) {
                    sieve_and(ctx, &m, w1, w2)
                } else {
                    sieve_mul(ctx, &m, w1, w2)
                };
                rep::Post::new(w, r)
            }
            (false, _) => {
                let y = *get_vbool(y0);
                if y {f1(x0)} else {f0()}
            }
            (_, false) => {
                let x = *get_vbool(x0);
                if x {f1(y0)} else {f0()}
            }
            _ => r,
        }
    } else {
        r
    }
}

#[allow(unused)]
pub fn or(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
    y0: &Value,
) -> Value {
    let r = if is_unknown(x0) || is_unknown(y0) {
        ctx.unknown.clone()
    } else {
        let x = *get_vbool(x0);
        let y = *get_vbool(y0);
        let z = x || y;
        rep::Bool::new(z)
    };
    if NEED_REL && s == Post {
        let c1 = is_bool_const_or_pre(x0);
        let c2 = is_bool_const_or_pre(y0);
        let m_orig = &m;
        if m.ring_type == RingBitwise {
            todo!("Bitwise booleans not fully implemented yet");
        }
        let m = match m.modulus {
            Some(ref m) => m,
            _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
        };
        let f0 = |x : &Value| x.clone();
        let f1 = || rep::Bool::new(true);
        match (c1, c2) {
            (false, false) => {
                let w1 = get_wire(x0);
                let w2 = get_wire(y0);
                let w = if is_nat_boolean(m_orig) {
                    let x_xor_y = sieve_xor(ctx, m_orig, w1, w2);
                    let x_and_y = sieve_and(ctx, m_orig, w1, w2);
                    sieve_xor(ctx, m_orig, &x_xor_y, &x_and_y)
                } else {
                    let x_plus_y = sieve_add(ctx, m_orig, w1, w2);
                    let x_times_y = sieve_mul(ctx, m_orig, w1, w2);
                    let minus_x_times_y = sieve_mulc(ctx, m_orig, &x_times_y, &(m - 1));
                    sieve_add(ctx, m_orig, &x_plus_y, &minus_x_times_y)
                };
                rep::Post::new(w, r)
            }
            (false, _) => {
                let y = *get_vbool(y0);
                if y {f1()} else {f0(x0)}
            }
            (_, false) => {
                let x = *get_vbool(x0);
                if x {f1()} else {f0(y0)}
            }
            _ => r,
        }
    } else {
        r
    }
}

#[allow(unused)]
pub fn xor(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
    y0: &Value,
) -> Value {
    let r = if is_unknown(x0) || is_unknown(y0) {
        ctx.unknown.clone()
    } else {
        let x = get_vbool(x0);
        let y = get_vbool(y0);
        let z = x ^ y;
        rep::Bool::new(z)
    };
    if NEED_REL && s == Post {
        if is_nat_boolean(m) {
            let c1 = is_bool_const_or_pre(x0);
            let c2 = is_bool_const_or_pre(y0);
            let f0 = |x : &Value| x.clone();
            let f1 = |x,r| {
                let w1 = get_wire(x);
                let w = sieve_not(ctx, m, w1);
                rep::Post::new(w, r)
            };
            match (c1, c2) {
                (false, false) => {
                    let w1 = get_wire(x0);
                    let w2 = get_wire(y0);
                    let w = sieve_xor(ctx, m, w1, w2);
                    rep::Post::new(w, r)
                }
                (false, _) => {
                    let y = *get_vbool(y0);
                    if y {f1(x0,r)} else {f0(x0)}
                }
                (_, false) => {
                    let x = *get_vbool(x0);
                    if x {f1(y0,r)} else {f0(y0)}
                }
                _ => r,
            }
        } else {
            let c1 = is_bool_const_or_pre(x0);
            let c2 = is_bool_const_or_pre(y0);
            let m_orig = m;
            if m.ring_type == RingBitwise {
                todo!("Bitwise booleans not fully implemented yet");
            }
            let m = match m.modulus {
                Some(ref m) => m,
                _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
            };
            let f0 = |x : &Value| x.clone();
            let f1 = |x,r| {
                let w1 = get_wire(x);
                let minus_x = sieve_mulc(ctx, &m_orig, w1, &(m - 1));
                let w = sieve_addc(ctx, &m_orig, &minus_x, &ctx.integer_one);
                rep::Post::new(w, r)
            };
            match (c1, c2) {
                (false, false) => {
                    let w1 = get_wire(x0);
                    let w2 = get_wire(y0);
                    let x_plus_y = sieve_add(ctx, &m_orig, w1, w2);
                    let x_times_y = sieve_mul(ctx, &m_orig, w1, w2);
                    let minus2_x_times_y = sieve_mulc(ctx, &m_orig, &x_times_y, &(m - 2));
                    let w = sieve_add(ctx, &m_orig, &x_plus_y, &minus2_x_times_y);
                    rep::Post::new(w, r)
                }
                (false, _) => {
                    let y = *get_vbool(y0);
                    if y {f1(x0,r)} else {f0(x0)}
                }
                (_, false) => {
                    let x = *get_vbool(x0);
                    if x {f1(y0,r)} else {f0(y0)}
                }
                _ => r,
            }
        }
    } else {
        r
    }
}

#[allow(unused)]
pub fn not(
    ctx: &ContextRef,
    m: &NatType,
    s: StageType,
    d: DomainType,
    x0: &Value,
) -> Value {
    let r = if is_unknown(x0) {
        ctx.unknown.clone()
    } else {
        let x = get_vbool(x0);
        let z = !x;
        rep::Bool::new(z)
    };
    if NEED_REL && s == Post {
        if is_nat_boolean(m) {
            let c1 = is_bool_const_or_pre(x0);
            match c1 {
                false => {
                    let w1 = get_wire(x0);
                    let w = sieve_not(ctx, m, w1);
                    rep::Post::new(w, r)
                }
                _ => r,
            }
        } else {
            let c1 = is_bool_const_or_pre(x0);
            let m_orig = m;
            if m.ring_type == RingBitwise {
                todo!("Bitwise booleans not fully implemented yet");
            }
            let m = match m.modulus {
                Some(ref m) => m,
                _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
            };
            match c1 {
                false => {
                    let w1 = get_wire(x0);
                    let minus_x = sieve_mulc(ctx, &m_orig, w1, &(m - 1));
                    let w = sieve_addc(ctx, &m_orig, &minus_x, &Integer::one());
                    rep::Post::new(w, r)
                }
                _ => r,
            }
        }
    } else {
        r
    }
}

/*
// like Haskell's `mod` (as opposed to `rem`)
#[allow(unused)]
fn hmod(x: &Integer, y: &Integer) -> Integer {
    x.mod_floor(y)
}

// like Haskell's `div` (as opposed to `quot`)
#[allow(unused)]
fn hdiv(x: &Integer, y: &Integer) -> Integer {
    x.div_floor(y)
}
 */

#[allow(unused)]
pub fn div(ctx: &ContextRef, m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> Value {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        ctx.unknown.clone()
    } else {
        (m.div)(get_int(x0),get_int(y0))
    }
}

#[allow(unused)]
pub fn modulo(ctx: &ContextRef, m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> Value {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        ctx.unknown.clone()
    } else {
        (m.hmod)(get_int(x0),get_int(y0))
    }
}

#[allow(unused)]
pub fn __mod_invert(ctx: &ContextRef, d: DomainType, x0: &Value, y0: &Value) -> Value {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        ctx.unknown.clone()
    } else {
        let x = x0.unwrap::<BigInt>();
        let y = y0.unwrap::<BigInt>();
        let e = &num_integer::Integer::extended_gcd(x, y);
        assert_eq!(e.gcd, Integer::one(), "Value {} not invertible modulo {}", x, y);
        let r = num_integer::Integer::mod_floor(&e.x, y);
        assert!(&r < y && (x * &r) % y == Integer::one(), "__mod_invert: r = {}, y = {}, x = {}", &r, y, x); // may be removed after it has been tested enough
        Value::new::<BigInt>(r)
     }
 }

#[allow(unused)]
pub fn mod_div(ctx: &ContextRef, m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> Value {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        ctx.unknown.clone()
    } else {
        (m.mod_div)(get_int(x0),get_int(y0))
    }
}

#[allow(unused)]
pub fn eq(ctx: &ContextRef, _m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> bool {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        false
    } else {
        (_m.eq)(x0,y0)
    }
}

#[allow(unused)]
pub fn neq(ctx: &ContextRef, _m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> bool {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        false
    } else {
        !(_m.eq)(x0,y0)
    }
}

#[allow(unused)]
pub fn lt(ctx: &ContextRef, _m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> bool {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        false
    } else {
        (_m.lt)(x0,y0)
    }
}

#[allow(unused)]
pub fn leq(ctx: &ContextRef, _m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> bool {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        false
    } else {
        !(_m.lt)(y0,x0)
    }
}

#[allow(unused)]
pub fn gt(ctx: &ContextRef, _m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> bool {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        false
    } else {
        (_m.lt)(y0,x0)
    }
}

#[allow(unused)]
pub fn geq(ctx: &ContextRef, _m: &NatType, d: DomainType, x0: &Value, y0: &Value) -> bool {
    if d > CURR_DOMAIN || (is_unknown(x0) || is_unknown(y0)) {
        false
    } else {
        !(_m.lt)(x0,y0)
    }
}

#[allow(unused)]
pub fn field_bit_width(_ctx: &ContextRef, x: &Value) -> u64 {
    get_pre_uint_inf(x).bits()
}

fn to_string1(ctx: &ContextRef, t: &Type, x: &Value) -> String {
    if is_unknown(x) {
        return "Unknown".to_string();
    }
    match t {
        TUnit => "()".to_string(),
        TBool(_) => x.unwrap::<rep::Bool>().0.to_string(),
        TUInt(m) => format!("{}", ZkscIntDisplay::new(m, x)),
        TList(elem_type) => {
            match elem_type {
                TQualify(t, _, d) => {
                    let mut s = String::new();
                    for i in 0 .. length_helper(x) {
                        s += &to_string1(ctx, t, &index_array_polymorphic_helper(ctx, d.clone(), x, i));
                    }
                    s
                }
                _ => panic!("Unexpected type to to_string1: {:?}", elem_type),
            }
        },
        TQualify(t, _, _) => to_string1(ctx, t, x),
        _ => panic!("Unexpected type to to_string1: {:?}", t),
    }
}

#[allow(unused)]
pub fn to_string(ctx: &ContextRef, t: &Type, _d: DomainType, x: &Value) -> Value {
    if is_unknown(x) {
        ctx.unknown.clone()
    } else {
        rep::Str::new(to_string1(ctx, t, x))
    }
}

#[allow(unused)]
pub fn string_append(ctx: &ContextRef, _d: DomainType, x: &Value, y: &Value) -> Value {
    if is_unknown(x) || is_unknown(y) {
        ctx.unknown.clone()
    } else {
        rep::Str::new(get_vstr(x).to_owned() + get_vstr(y))
    }
}

#[allow(unused)]
pub fn dbg_print(ctx: &ContextRef, d: DomainType, s: &Value) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        let s = get_vstr(s);
        let w = sieve_backend().get_next_wire_number();
        let r = sieve_backend().get_rel_file_size();
        if w > 0 {
            let w_str = format!("{:10}", w);
            let r_str = format!("{:9}", r);
            debug!("[wire:{w_str}, rel:{r_str}] {s}");
        } else if r > 0 {
            let r_str = format!("{:9}", r);
            debug!("[rel:{r_str}] {s}");
        } else {
            debug!("{s}");
        }
    }
}

#[allow(unused)]
pub fn assert_zero(ctx: &ContextRef, d: DomainType, m: &NatType, x0: &Value) {
    if d <= CURR_DOMAIN && !is_unknown(x0) && !ctx.inside_sieve_fn_def() {
        if !(m.is_zero)(get_int(x0)) {
            zksc_assert_error!(ctx, "assertion failed: variable has non-zero value {}", ((m.to_bigint)(get_int(x0))));
        }
    }
    if NEED_REL && !is_int_const_or_pre(x0) {
        let w = get_wire(x0);
        sieve_assert_zero(ctx, &m, w);
    }
}

#[allow(unused)]
pub fn dbg_assert(ctx: &ContextRef, d: DomainType, m1: &NatType, x0: &Value, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        match x0.view() {
            ValueView::Unknown(_) => {},
            ValueView::Bool(x) => {
                if !x {
                    zksc_panic!(ctx, "{}Debug assertion failed at {}", err, loc);
                }
            },
            ValueView::ZkscDefined() => {
                if !(m1.is_one)(x0) {
                    zksc_panic!(ctx, "{}Debug assertion failed at {}", err, loc);
                }
            },
            _ => zksc_panic!(ctx, "Invalid argument to dbg_assert: {:?}", x0),
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_bool(ctx: &ContextRef, d: DomainType, x: bool, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        if !x {
            zksc_panic!(ctx, "{}Debug assertion failed at {}", err, loc);
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_eq(ctx: &ContextRef, d: DomainType, m: &NatType, x0: &Value, y0: &Value, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        match (x0.view(), y0.view()) {
            (ValueView::Unknown(_),_) => {},
            (_,ValueView::Unknown(_)) => {},
            (ValueView::Bool(x), ValueView::Bool(y)) => {
                if x != y {
                    zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
                }
            }
            (ValueView::ZkscDefined(), ValueView::ZkscDefined()) => {
                if !(m.eq)(x0,y0) {
                    zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
                }
            }
            _ => zksc_panic!(ctx, "Invalid arguments to dbg_assert_eq: {:?}, {:?}", x0, y0),
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_eq_u8(ctx: &ContextRef, d: DomainType, x: u8, y: u8, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        if x != y {
            zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_eq_u16(ctx: &ContextRef, d: DomainType, x: u16, y: u16, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        if x != y {
            zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_eq_u32(ctx: &ContextRef, d: DomainType, x: u32, y: u32, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        if x != y {
            zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_eq_u64(ctx: &ContextRef, d: DomainType, x: u64, y: u64, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        if x != y {
            zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
        }
    }
}

#[allow(unused)]
pub fn dbg_assert_eq_u128(ctx: &ContextRef, d: DomainType, x: u128, y: u128, loc: &str, err: &str) {
    if DEBUG && d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        if x != y {
            zksc_panic!(ctx, "{}Debug equality assertion failed at {}", err, loc);
        }
    }
}

#[allow(unused)]
pub fn assert(ctx: &ContextRef, d: DomainType, m: &NatType, x0: &Value) {
    if d <= CURR_DOMAIN && !is_unknown(x0) && !ctx.inside_sieve_fn_def() {
        let x = get_vbool(x0);
        if !x {
            zksc_assert_error!(ctx, "assertion failed: variable has value {}", x);
        }
    }
    if NEED_REL && !is_bool_const_or_pre(x0) {
        if is_nat_boolean(m) {
            let w1 = get_wire(x0);
            let w = sieve_not(ctx, m, w1);
            sieve_assert_zero(ctx, m, &w);
        } else {
            let m_orig = m;
            let m = match m.modulus {
                Some(ref m) => m,
                _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
            };
            let w1 = get_wire(x0);
            let x_minus_1 = sieve_addc(ctx, &m_orig, w1, &(m - 1));
            sieve_assert_zero(ctx, &m_orig, &x_minus_1);
        }
    }
}

#[allow(unused)]
pub fn assert_eq(ctx: &ContextRef, t1: &Type, t2: &Type, d: DomainType, x0: &Value, y0: &Value) {
    let x_pre = cast_to_pre(x0);
    let y_pre = cast_to_pre(y0);
    if d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        match (x_pre.view(), y_pre.view()) {
            (ValueView::ZkscDefined(),ValueView::ZkscDefined()) => {
                let (m1,m2) = match (t1, t2) {
                    (TUInt(m1), TUInt(m2)) => (m1,m2),
                    (TBool(m1), TBool(m2)) => (m1,m2),
                    _ => zksc_panic!(ctx, "Mismatching types in assert_eq: {:?} / {:?}", t1, t2),
                };
                let assertion_failed = if m1.modulus == m2.modulus {
                    ! (m1.eq)(x_pre,y_pre)
                } else {
                    // TODO: this may be inefficient
                    // but the previous code did not work at all when the moduli were different
                    // and the ZKSC assert_eq is called mostly for arguments from different moduli.
                    (m1.to_bigint)(x_pre) != (m2.to_bigint)(y_pre)
                };
                if assertion_failed {
                    zksc_assert_error!(ctx,"assert_eq({},{})", ZkscIntDisplay::new(m1, x_pre), ZkscIntDisplay::new(m2, y_pre));
                }
            }
            (ValueView::Bool(x), ValueView::Bool(y)) => {
                if x != y {
                    zksc_assert_error!(ctx, "equality assertion failed: {} != {}", x, y);
                }
            },
            _ => zksc_panic!(ctx, "Mismatching types in assert_eq: {:?} / {:?}", x_pre, y_pre),
        }
    }
    if NEED_REL {
        let b1 = is_const_or_pre(x0);
        let b2 = is_const_or_pre(y0);
        let (m1,m2) = match (t1, t2) {
            (TUInt(m1), TUInt(m2)) => (m1,m2),
            (TBool(m1), TBool(m2)) => (m1,m2),
            _ => zksc_panic!(ctx, "Mismatching types in assert_eq: {:?} / {:?}", t1, t2),
        };
        if b1 ^ b2 {
            zksc_panic!(ctx, "TODO: assert_eq with one (but not both) arguments constant not yet implemented: {:?} / {:?}", x0, y0);
        } else if !(b1 || b2) {
            if m1.tag == m2.tag {
                //let m = Nat(m1.clone());
                let m = match m1.modulus { Some(ref m) => m, _ => zksc_panic!(ctx, "Infinite modulus not supported") };
                let w1 = get_wire(x0);
                let w2 = get_wire(y0);
                let w2_neg = sieve_mulc(ctx, m1, w2, &(m - 1));
                let w = sieve_add(ctx, m1, w1, &w2_neg);
                sieve_assert_zero(ctx, m1, &w);
            } else {
                sieve_assert_eq(ctx, m1, get_wire(x0), m2, get_wire(y0));
            }
        }
    }
}

#[allow(unused)]
pub fn assert_eq_uints_bools(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, bs: &Value) {
    let xs = get_varray(xs);
    assert_eq!(xs.len(), 1, "The uints argument of assert_eq_uints_bools must have length 1");
    let x = &xs[0];
    if d <= CURR_DOMAIN && !ctx.inside_sieve_fn_def() {
        let x = get_int(x);
        let uint_value = &(m.to_bigint)(x);
        let mut total = Integer::zero();
        let mut curr = Integer::one();
        let bool_values = get_varray(bs).iter().map(get_vbool);
        for b in bool_values.clone() {
            if *b { total += &curr; }
            curr *= 2isize;
        }

        if uint_value != &total {
            zksc_assert_error!(ctx, "assert_eq_uints_bools: assertion failed: {} != {:?}", uint_value, bool_values.collect::<Vec<_>>());
        }
    }
    if NEED_REL {
        let uint_wire = get_or_create_wire(m, x);
        let mod2 = ctx.nat_2();
        let bool_wires = get_varray(bs).iter().map(|x| get_or_create_bool2_wire(ctx, mod2, x)).collect();
        sieve_assert_eq_scalar_vec(ctx, m, &uint_wire, mod2, bool_wires);
    }
}

fn wire_uint(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value) -> Value {
    if d == Public {
        return x.clone();
    }
    if ctx.inside_sieve_fn_def() {
        if !NEED_REL {
            return x.clone();
        }
        let w = match d {
            Verifier => sieve_backend().get_instance(&m),
            Prover => {
                let witness_count = *ctx.sieve_fn_witness_count.borrow() + 1;
                *ctx.sieve_fn_witness_count.borrow_mut() = witness_count;
                sieve_backend().get_witness(&m)
            }
            _ => unreachable!(),
        };
        return rep::Post::new(w, x.clone());
    }
    if ctx.inside_sieve_fn_call() {
        match d {
            Verifier => sieve_backend().add_instance(&m, x),
            Prover => sieve_backend().add_witness(&m, x),
            _ => unreachable!(),
        }
        return x.clone();
    }

    match d {
        Verifier => sieve_add_instance(ctx, m, x),
        Prover => sieve_add_witness(ctx, m, x),
        _ => unreachable!(),
    };

    if NEED_REL {
        let w =
            match d {
                Verifier => sieve_get_instance(ctx, m),
                Prover => sieve_get_witness(ctx, m),
                _ => unreachable!(),
            };

        rep::Post::new(w, x.clone())
    }
    else {
        x.clone()
    }
}

fn wire_bool(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value) -> Value {
    if d == Public {
        return x.clone();
    }
    let m_orig = m;
    if ctx.inside_sieve_fn_def() {
        if !NEED_REL {
            return x.clone();
        }
        let w = match d {
            Verifier => sieve_backend().get_instance(&m_orig),
            Prover => {
                let w = sieve_backend().get_witness(&m_orig);
                // For bool[N] @prover (N > 2), check that the value is a bit.
                let ring_type = m.ring_type;
                let m = match m.modulus {
                    Some(ref m) => m,
                    _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
                };
                if m > &Integer::from(2) {
                    if ring_type == RingBitwise {
                        let x_plus_1 = sieve_addc(ctx, &m_orig, &w, &ctx.integer_one);
                        let x_times_x_plus_1 = sieve_mul(ctx, &m_orig, &x_plus_1, &w);
                        sieve_assert_zero(ctx, &m_orig, &x_times_x_plus_1);
                    } else {
                        let x2 = sieve_mul(ctx, &m_orig, &w, &w);
                        let x2_minus_x = sieve_backend().sub(&m_orig, &x2, &w);
                        sieve_assert_zero(ctx, &m_orig, &x2_minus_x);
                    }
                }
                w
            }
            _ => unreachable!(),
        };
        return rep::Post::new(w, x.clone());
    }
    if ctx.inside_sieve_fn_call() {
        match d {
            Verifier => sieve_backend().add_instance(&m_orig, x),
            Prover => sieve_backend().add_witness(&m_orig, x),
            _ => unreachable!(),
        }
        return x.clone();
    }

    match d {
        Verifier => sieve_add_instance(ctx, &m_orig, x),
        Prover => sieve_add_witness(ctx, &m_orig, x),
        _ => unreachable!(),
    };

    if ! NEED_REL {
        return x.clone();
    }

    let w =
        match d {
            Verifier => sieve_get_instance(ctx, &m_orig),
            Prover => {
                let w = sieve_get_witness(ctx, &m_orig);
                // For bool[N] @prover (N > 2), check that the value is a bit.
                let ring_type = m.ring_type;
                let m = match m.modulus {
                    Some(ref m) => m,
                    _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
                };
                if m > &Integer::from(2) {
                    if ring_type == RingBitwise {
                        let x_plus_1 = sieve_addc(ctx, &m_orig, &w, &ctx.integer_one);
                        let x_times_x_plus_1 = sieve_mul(ctx, &m_orig, &x_plus_1, &w);
                        sieve_assert_zero(ctx, &m_orig, &x_times_x_plus_1);
                    } else {
                        let x2 = sieve_mul(ctx, &m_orig, &w, &w);
                        let minus_x = sieve_mulc(ctx, &m_orig, &w, &(m - 1));
                        let x2_minus_x = sieve_add(ctx, &m_orig, &x2, &minus_x);
                        sieve_assert_zero(ctx, &m_orig, &x2_minus_x);
                    }
                }
                w
            }
            _ => unreachable!(),
        };

    rep::Post::new(w, x.clone())
}

#[allow(unused)]
pub fn wire(ctx: &ContextRef, t: &Type, xlen: &Value, x: &Value) -> Value {
    let (u, d) = match t {
        TQualify(u, _, d) => (u, d),
        _ => zksc_panic!(ctx, "wire: invalid type"),
    };

    match u {
        TBool(m) => wire_bool(ctx, m, *d, x),
        TUInt(m) => wire_uint(ctx, m, *d, x),
        TList(t) => {
            match xlen.view() {
                ValueView::Array(xlen) => {
                    if is_unknown(x) {
                        rep::Array::new(xlen.iter().map(|xlen| wire(ctx, t, xlen, x)).collect())
                    } else {
                        let x = get_varray(x);
                        assert_eq!(xlen.len(), x.len(), "Lengths of the arguments of the wire construct do not match");
                        rep::Array::new(xlen.iter().zip(x.iter()).map(|(xlen,x)| wire(ctx, t, xlen, x)).collect())
                    }
                }
                ValueView::ArrayUnit(len) => {
                    if is_unknown(x) {
                        rep::Array::new(iter::repeat(()).take(*len).map(|_| wire(ctx, t, &ctx.scalar, x)).collect())
                    } else {
                        match x.view() {
                            ValueView::Array(x) => {
                                assert_eq!(*len, x.len(), "Lengths of the arguments of the wire construct do not match");
                                rep::Array::new(x.iter().map(|x| wire(ctx, t, &ctx.scalar, x)).collect())
                            }
                            ValueView::ArrayBool(x) => {
                                assert_eq!(*len, x.len(), "Lengths of the arguments of the wire construct do not match");
                                let (u, d) = match t {
                                    TQualify(u, _, d) => (u, d),
                                    _ => zksc_panic!(ctx, "wire: invalid type"),
                                };
                                match u {
                                    TBool(m) => rep::Array::new(x.iter().map(|x| wire_bool(ctx, m, *d, &bool_to_value(ctx, *d, *x))).collect()),
                                    _ => panic!("wire"),
                                }
                            }
                            _ => panic!("wire"),
                        }
                    }
                }
                _ => panic!("wire: elements of the shape argument are not unit values"),
            }
        }
        TTuple(ts) => {
            if is_unknown(x) {
                StructInner::new_tuple(ts.iter().zip(get_varray(xlen).iter()).map(|(t,xlen)| wire(ctx, t, xlen, x)).collect())
            } else {
                StructInner::new_tuple(ts.iter().zip(get_varray(xlen).iter().zip(get_varray(x).iter())).map(|(t,(xlen,x))| wire(ctx, t, xlen, x)).collect())
            }
        }
        _ => zksc_panic!(ctx, "wire: invalid type"),
    }
}

fn cast_to_correct_moduli(ctx : &ContextRef, t: &Type, x: &Value) -> Value {
    match t {
        TQualify(u, _, _) => cast_to_correct_moduli(ctx,u, x),
        TBool(_) => x.clone(),
        TUInt(m) => cast_to_uint(ctx,Pre,ctx.nat_inf(),x,m),
        TList(t) => rep::Array::new(get_varray(x).iter().map(|x| cast_to_correct_moduli(ctx,t, x)).collect()),
        TTuple(ts) => StructInner::new_tuple(get_varray(x).iter().zip(ts.iter()).map(|(x,t)| cast_to_correct_moduli(ctx,t, x)).collect()),
        t => zksc_panic!(ctx, "cast_to_correct_moduli: unsupported type of get_public/instance/witness return value: {:?}", t),
    }
}

#[allow(unused)]
pub fn get_public(ctx: &ContextRef, t: &Type, _s: StageType, _d: DomainType, x: &Value) -> Value {
    let x = get_vstr(x);
    let v = match ctx.input_public.get(x) {
        Some(v) => v,
        None => zksc_panic!(ctx, "missing value {} in public json", x),
    };
    cast_to_correct_moduli(ctx,t, v)
}

#[allow(unused)]
pub fn get_instance(ctx: &ContextRef, t: &Type, _s: StageType, _d: DomainType, x: &Value) -> Value {
    if CURR_DOMAIN >= Verifier {
        let x = get_vstr(x);
        let v = match ctx.input_instance.get(x) {
            Some(v) => v,
            None => zksc_panic!(ctx, "missing value {} in instance json", x),
        };
        cast_to_correct_moduli(ctx,t, v)
    } else {
        ctx.unknown.clone()
    }
}

#[allow(unused)]
pub fn get_witness(ctx: &ContextRef, t: &Type, _s: StageType, _d: DomainType, x: &Value) -> Value {
    if CURR_DOMAIN == Prover && !ctx.inside_sieve_fn_def() {
        let x = get_vstr(x);
        let v = match ctx.input_witness.get(x) {
            Some(v) => v,
            None => zksc_panic!(ctx, "missing value {} in witness json", x),
        };
        cast_to_correct_moduli(ctx,t, v)
    } else {
        ctx.unknown.clone()
    }
}

fn is_even(n: usize) -> bool {
    n % 2 == 0
}

fn make_waksman_network(n: usize) -> Vec<usize> {
    if n == 1 {
        vec![0]
    } else if n == 2 {
        vec![0, 1, 2, 3]
    } else {
        let halfnfloor = n / 2;
        let halfnceil = n - halfnfloor;
        let upperhalf = make_waksman_network(halfnfloor);
        let lowerhalf = make_waksman_network(halfnceil);
        let upperlen = upperhalf.len() - halfnfloor; // The size of the upper WN, except its output wires
        let lowerlen = lowerhalf.len() - halfnceil; // The size of the lower WN, except its output wires
        let leftlen = if is_even(n) { n } else { n - 1 }; // The number of input ports of the initial switches; equals twice halfnfloor
        let totallen = upperlen + lowerlen + 2 * n - 2; // Twice the number of switches; by n less than the number of wires
        let convert_upper = |x: usize| { // Finding the number of an element of the upper WN in the whole WN
            if x < halfnfloor { // Input wires of the upper WN
                n + x * 2 // Conversion to the ordering of the whole WN
            } else { // Output ports of the upper WN
                n + leftlen - halfnfloor + x // Conversion to the ordering of the whole WN
            }
        };
        let convert_lower = |x: usize| { // Finding the number of an element of the lower WN in the whole WN
            if x < halfnceil { // Input wires of the lower WN
                if (x == (halfnceil - 1)) && !is_even(n) { // The last input wire in the case of odd n
                    n - 1
                } else { // Other input wires
                    n + 1 + x * 2 // Conversion to the ordering of the whole WN
                } 
            } else { // Output ports of the lower WN
                n + leftlen + upperlen - halfnceil + x // Conversion to the ordering of the whole WN
            }
        };
        let mut res = Vec::new();
        res.reserve(totallen + n);
        for i in 0 .. totallen + n {
            let r =
                if i < leftlen { i } // Input ports of the initial switches connect the input wires (for odd n, the last input wire is not included)
                else if i < leftlen + upperlen { // Input ports of the switches of the upper WN
                    convert_upper(upperhalf[i - leftlen])
                } else if i < leftlen + upperlen + lowerlen { // Input ports of the switches of the lower WN
                    convert_lower(lowerhalf[i - leftlen - upperlen])
                } else if i < totallen { // Input ports of the final switches
                    let inpc = i - leftlen - upperlen - lowerlen; // The number in order among the input ports of the final switches
                    let inpsw = inpc / 2; // The number of the final switch
                    if is_even(inpc) { // The upper input port of the final switch
                        convert_upper(upperhalf[upperlen + inpsw])
                    } else { // The lower input port of the final switch
                        convert_lower(lowerhalf[lowerlen + inpsw])
                    }
                } else if is_even(n) { // Output wires, even n
                    if i < totallen + n - 2 { // Not among the last two output wires
                        i + 2 // By 2 larger since the last two output wires are not connected to any final switch
                    } else if i == totallen + n - 2 { // The second last output wire
                        convert_upper(upperhalf[upperlen + halfnfloor - 1])
                    } else { // The last output wire
                        convert_lower(lowerhalf[lowerlen + halfnceil - 1])
                    }
                } else if i < totallen + n - 1 { // Output wires, odd n, not the last output wire
                    i + 1 // By 1 larger since the last wire is not connected to any final switch
                } else { // Odd n, the last output wire
                    convert_lower(lowerhalf[lowerlen + halfnceil - 1])
                };
            res.push(r);
        }
        res
    }
}

#[allow(unused)]
pub fn __make_waksman_network(ctx: &ContextRef, n: u64) -> Value {
    let n = n.to_usize().unwrap();
    let wn = make_waksman_network(n);
    let wn = wn.into_iter().map(|x| x as u64).collect();
    rep::ArrayU64::new(wn)
}

#[allow(unused)]
fn get_sorting_permutation<K: Ord>(xs: &Vec<K>) -> Vec<usize> {
    let mut ys: Vec<_> = (0usize..).zip(xs.iter()).collect();
    ys.sort_by_key(|x| x.1);
    ys.iter().map(|x| x.0).collect()
}

#[allow(unused)]
pub fn __get_sorting_permutation(ctx: &ContextRef, d: DomainType, xs: &Value) -> Value {
    if is_unknown(xs) {
        ctx.unknown.clone()
    } else if d > CURR_DOMAIN {
        //rep::Array::new(get_varray(xs).iter().map(|_| ctx.unknown.clone()).collect())
        let mut res = Vec::new();
        res.resize(length_helper(xs), 0);
        rep::ArrayU64::new(res)
    } else {
        let res = match xs.view() {
            ValueView::Array(xs) => {
                let m = ctx.nat_inf();
                get_sorting_permutation(&xs.iter().map(|x| get_pre_or_post_uint(m, x)).collect())
            }
            //ValueView::ArrayU64(xs) => get_sorting_permutation(xs),
            _ => panic!("__get_sorting_permutation"),
        };
        rep::ArrayU64::new(res.into_iter().map(|x| x as u64).collect())
    }
}

fn accompanying(x: usize) -> usize {
    4 * (x / 2) + 1 - x
}

fn permutation_switches_len(n: usize) -> usize {
    if n == 0 { panic!("__permutation_switches: indices must not be empty"); }
    else if n == 1 { 0 }
    else {
        let upperperm_len = n / 2;
        let lowerperm_len = n - upperperm_len;
        let upperswitches_len = permutation_switches_len(upperperm_len);
        let lowerswitches_len = permutation_switches_len(lowerperm_len);
        upperswitches_len + lowerswitches_len + n - 1
    }
}

fn permutation_switches(indices: Vec<usize>) -> Vec<bool> {
    let n = indices.len();
    if n == 0 { panic!("__permutation_switches: indices must not be empty"); }
    else if n == 1 { vec![] }
    else {
        let halfnfloor = n / 2;
        let halfnceil = n - halfnfloor;
        let mut inverseperm = Vec::new();
        inverseperm.resize(n, 0);
        for i in 0 .. n { inverseperm[indices[i]] = i; }
        let mut initial_colors = Vec::new();
        initial_colors.resize(n, 0);
        let mut final_colors = Vec::new();
        final_colors.resize(n, 0);
        for i in 1 .. n + 1 {
            if final_colors[n - i] == 0 {
                let mut y;
                let mut x;
                let mut x_;
                let mut y_ = 0;
                for j in 0 .. halfnceil {
                    y = if j == 0 { n - i } else { accompanying(y_) };
                    if final_colors[y] > 0 { break; }
                    x = indices[y];
                    final_colors[y] = 2;
                    initial_colors[x] = 2;
                    if x == 2 * halfnfloor { break; }
                    x_ = accompanying(x);
                    y_ = inverseperm[x_];
                    initial_colors[x_] = 1;
                    final_colors[y_] = 1;
                };
            };
        };
        let mut initialswitches = Vec::new();
        initialswitches.reserve(halfnfloor);
        for k in 0 .. halfnfloor { initialswitches.push(initial_colors[2 * k] < initial_colors[2 * k + 1]) };
        let mut finalswitches = Vec::new();
        finalswitches.reserve(halfnceil - 1);
        for k in 0 .. halfnceil - 1 { finalswitches.push(final_colors[2 * k] < final_colors[2 * k + 1]) };
        let mut upperperm = Vec::new();
        upperperm.reserve(halfnfloor);
        for k in 0 .. halfnfloor {
            upperperm.push(
                if 2 * k == n - 2 { indices[n - 2] / 2 }
                else { indices[2 * k + usize::from(!finalswitches[k])] / 2 }
            );
        };
        let mut lowerperm = Vec::new();
        lowerperm.reserve(halfnceil);
        for k in 0 .. halfnceil {
            lowerperm.push(
                if k == halfnceil - 1 { indices[n - 1] / 2 }
                else { indices[2 * k + usize::from(finalswitches[k])] / 2 }
            );
        };
        let upperswitches = permutation_switches(upperperm);
        let lowerswitches = permutation_switches(lowerperm);
        let mut res = Vec::new();
        res.reserve(upperswitches.len() + lowerswitches.len() + n - 1);
        for i in 0 .. upperswitches.len() + lowerswitches.len() + n - 1 {
            res.push(
                if i < halfnfloor { initialswitches[i] }
                else if i < halfnfloor + upperswitches.len() { upperswitches[i - halfnfloor] }
                else if i < halfnfloor + upperswitches.len() + lowerswitches.len() { lowerswitches[i - halfnfloor - upperswitches.len()] }
                else { finalswitches[i - halfnfloor - upperswitches.len() - lowerswitches.len()] }
            );
        }
        res
    }
}

#[allow(unused)]
pub fn __permutation_switches(ctx: &ContextRef, d: DomainType, indices: &Value) -> Value {
    if is_unknown(indices) {
        ctx.unknown.clone()
    } else if d > CURR_DOMAIN {
        let switches_len = permutation_switches_len(length_helper(indices));
        let mut switches = Vec::new();
        switches.resize(switches_len, false);
        rep::ArrayBool::new(switches)
    } else {
        let indices = match indices.view() {
            ValueView::Array(xs) => xs.iter().map(|x| value_to_u64(x) as usize).collect(),
            ValueView::ArrayU64(xs) => xs.iter().map(|x| *x as usize).collect(),
            _ => panic!("__permutation_switches"),
        };
        let switches = permutation_switches(indices);
        rep::ArrayBool::new(switches)
    }
}

#[allow(unused)]
pub fn bitextract_pre_uint(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value, fbw: &Value) -> Value {
    let fbw = get_pre_uint_inf(fbw);
    let fbw = fbw.to_u64().expect("fbw does not fit into u64");
    let mut res: Vec<Value> = Vec::new();
    if d <= CURR_DOMAIN {
        let x = (m.to_bigint)(x);
        assert!(x.sign() != Sign::Minus, "bitextract_pre_uint: negative value");
        assert!(x.bits() <= fbw, "bitextract_pre_uint: value does not fit into the given number of bits");
        let zero = (m.from_bigint)(&ctx.integer_zero);
        let one = (m.from_bigint)(&ctx.integer_one);
        for i in 0 .. fbw {
            let b = x.bit(i);
            if b {
                res.push(one.clone());
            } else {
                res.push(zero.clone());
            }
        }
    } else {
        res.resize(fbw.to_usize().unwrap(), ctx.unknown.clone());
    }
    rep::Array::new(res)
}

pub fn __lt(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value, y: &Value) -> Value {
    let output_wires = sieve_backend().plugin_apply("extended_arithmetic_v1", "less_than", vec![], m, 1, vec![&get_or_create_wire(m, x), &get_or_create_wire(m, y)]);
    let w = sieve_clone_wire(ctx, m, &output_wires[0]);
    let x_pre = get_pre_value_from_post(x); 
    let y_pre = get_pre_value_from_post(y);
    let r =
        if d > CURR_DOMAIN || (is_unknown(x_pre) || is_unknown(y_pre)) {
            ctx.unknown.clone()
        } else {
            rep::Bool::new((m.lt)(x_pre,y_pre))
        };
    rep::Post::new(w, r)
}

#[allow(unused)]
pub fn __le(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value, y: &Value) -> Value {
    let output_wires = sieve_backend().plugin_apply("extended_arithmetic_v1", "less_than_equal", vec![], m, 1, vec![&get_or_create_wire(m, x), &get_or_create_wire(m, y)]);
    let w = sieve_clone_wire(ctx, m, &output_wires[0]);
    let x_pre = get_pre_value_from_post(x); 
    let y_pre = get_pre_value_from_post(y);
    let r =
        if d > CURR_DOMAIN || (is_unknown(x_pre) || is_unknown(y_pre)) {
            ctx.unknown.clone()
        } else {
            let x = (m.to_bigint)(x_pre);
            let y = (m.to_bigint)(y_pre);
            rep::Bool::new(x <= y)
        };
    rep::Post::new(w, r)
}

#[allow(unused)]
fn divmod(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value, y: &Value) -> (Value, Value) {
    let output_wires = sieve_backend().plugin_apply("extended_arithmetic_v1", "division", vec![], m, 2, vec![&get_or_create_wire(m, x), &get_or_create_wire(m, y)]);
    let w_quotient = sieve_clone_wire(ctx, m, &output_wires[0]);
    let w_remainder = sieve_clone_wire(ctx, m, &output_wires[1]);
    let x_pre = get_pre_value_from_post(x); 
    let y_pre = get_pre_value_from_post(y);
    let r =
        if d > CURR_DOMAIN || (is_unknown(x_pre) || is_unknown(y_pre)) {
            (ctx.unknown.clone(), ctx.unknown.clone())
        } else {
            let quotient = (m.div)(x_pre, y_pre);
            let remainder = (m.hmod)(x_pre, y_pre);
            (quotient, remainder)
        };
    (rep::Post::new(w_quotient, r.0), rep::Post::new(w_remainder, r.1))
}

#[allow(unused)]
pub fn __divmod(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value, y: &Value) -> Value {
    let (q, r) = divmod(ctx, m, d, x, y);
    StructInner::new_tuple(Box::new([q, r]))
}

#[allow(unused)]
pub fn __div(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value, y: &Value) -> Value {
    divmod(ctx, m, d, x, y).0
}

#[allow(unused)]
pub fn __bitextract(ctx: &ContextRef, m: &NatType, d: DomainType, x: &Value) -> Value {
    let modulus = m.modulus.clone().unwrap();
    let mut bw: usize = 0;
    let mut t: BigInt = ctx.integer_one.clone();
    while t < modulus {
        bw = bw + 1;
        t = 2 * t;
    }
    let output_wrs = sieve_backend().plugin_apply_wr("extended_arithmetic_v1", "bit_decompose", vec![], m, vec![bw], vec![&wire_to_wr(&get_or_create_wire(m, x))]);
    let x_pre = get_pre_value_from_post(x); 

    let zero = (m.from_bigint)(&ctx.integer_zero);
    let one = (m.from_bigint)(&ctx.integer_one);
    let mut bits = Vec::new();
    let r =
        if d > CURR_DOMAIN || is_unknown(x_pre) {
            for i in 0 .. bw {
                bits.push(ctx.unknown.clone());
            }
        } else {
            let x = (m.to_bigint)(x_pre);
            for i in 0 .. bw {
                let b = x.bit(i.to_u64().unwrap());
                if b {
                    bits.push(one.clone());
                } else {
                    bits.push(zero.clone());
                }
            }
        };
    bits = bits.into_iter().rev().collect();
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), bits)))
}



#[allow(unused)]
pub fn bitextract_vec_helper(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, fbw_u64: u64) -> Value {
    let fbw = fbw_u64.to_usize().expect("fbw does not fit into usize");
    let zero = (m.from_bigint)(&ctx.integer_zero);
    let one = (m.from_bigint)(&ctx.integer_one);
    let mut bitvecs_pre: Vec<Vec<Value>> = Vec::new();
    let xs = unslice_helper(xs);
    let xs = get_varray(&xs);
    let n = xs.len();
    for i in 0 .. fbw {
        let mut v = Vec::new();
        v.reserve(n);
        bitvecs_pre.push(v);
    }
    if d <= CURR_DOMAIN {
        for x in xs {
            let x = (m.to_bigint)(get_pre_value_from_post(x));
            assert!(x.sign() != Sign::Minus, "bitextract_pre_uint: negative value");
            assert!(x.bits() <= fbw_u64, "bitextract_pre_uint: value does not fit into the given number of bits");
            for i in 0 .. fbw {
                let b = x.bit(i.to_u64().unwrap());
                if b {
                    bitvecs_pre[i].push(one.clone());
                } else {
                    bitvecs_pre[i].push(zero.clone());
                }
            }
        }
    } else {
        for i in 0 .. fbw {
            bitvecs_pre[i].resize(n, ctx.unknown.clone());
        }
    }
    let mut bitvecs_post: Vec<Value> = Vec::new();
    for bits in bitvecs_pre {
        match d {
            Public => panic!("bitextract_vec_helper: @public elements not supported"),
            Verifier => {
                bits.iter().for_each(|x| {
                    sieve_backend().add_instance(m, x);
                });
            }
            Prover => {
                bits.iter().for_each(|x| {
                    sieve_backend().add_witness(m, x);
                });
            }
        };
        let wr =
            if NEED_REL {
                match d {
                    Public => panic!(),
                    Verifier => sieve_backend().get_instance_wr(m, bits.len()),
                    Prover => sieve_backend().get_witness_wr(m, bits.len()),
                }
            } else {
                sieve_backend().zero_wire_range(m, bits.len())
            };
        if use_iter_plugin(ctx) {
            let soa = SoA::Scalar((wr, bits));
            bitvecs_post.push(rep::PostSoA::new(soa));
        } else {
            let n = bits.len();
            let mut ys = Vec::with_capacity(n);
            for i in 0 .. n {
                ys.push(rep::Post::new(wr.index(i), bits[i].clone()));
            }
            bitvecs_post.push(rep::Array::new(ys));
        }
    }
    rep::Array::new(bitvecs_post)
}

fn uint_n_pre_matrix_prod_helper<T>(
        d: DomainType,
        rows: &Vec<Value>,
        cols: &Vec<Value>,
        zero: T,
        get_array: fn(&Value) -> &Vec<T>,
        new_array: fn(Vec<T>) -> Value,
        scalar_prod: fn(&Vec<T>, &Vec<T>) -> T,
        xss: &mut Vec<Value>)
        where T: Copy
{
    let nr = rows.len();
    let nc = cols.len();
    if d <= CURR_DOMAIN {
        let rows: Vec<&Vec<T>> = rows.iter().map(|row| {
            get_array(row)
        }).collect();
        let cols: Vec<&Vec<T>> = cols.iter().map(|col| {
            get_array(col)
        }).collect();
        let nk = rows[0].len();
        for i in 0 .. nr {
            assert!(rows[i].len() == nk);
        }
        for i in 0 .. nc {
            assert!(cols[i].len() == nk);
        }
        for i in 0 .. nr {
            let mut xs: Vec<T> = Vec::with_capacity(nc);
            for j in 0 .. nc {
                xs.push(scalar_prod(rows[i], cols[j]));
            }
            xss.push(new_array(xs));
        }
    } else {
        for _ in 0 .. nr {
            let mut xs: Vec<T> = Vec::with_capacity(nc);
            xs.resize(nc, zero);
            xss.push(new_array(xs));
        }
    }
}

fn scalar_prod_helper_u8(row: &Vec<u8>, col: &Vec<u8>) -> u8 {
    let mut s: u8 = 0;
    for k in 0 .. row.len() {
        s = s.wrapping_add(row[k].wrapping_mul(col[k]));
    }
    s
}

fn scalar_prod_helper_u16(row: &Vec<u16>, col: &Vec<u16>) -> u16 {
    let mut s: u16 = 0;
    for k in 0 .. row.len() {
        s = s.wrapping_add(row[k].wrapping_mul(col[k]));
    }
    s
}

fn scalar_prod_helper_u32(row: &Vec<u32>, col: &Vec<u32>) -> u32 {
    let mut s: u32 = 0;
    for k in 0 .. row.len() {
        s = s.wrapping_add(row[k].wrapping_mul(col[k]));
    }
    s
}

fn scalar_prod_helper_u64(row: &Vec<u64>, col: &Vec<u64>) -> u64 {
    let mut s: u64 = 0;
    for k in 0 .. row.len() {
        s = s.wrapping_add(row[k].wrapping_mul(col[k]));
    }
    s
}

fn scalar_prod_helper_u128(row: &Vec<u128>, col: &Vec<u128>) -> u128 {
    let mut s: u128 = 0;
    for k in 0 .. row.len() {
        s = s.wrapping_add(row[k].wrapping_mul(col[k]));
    }
    s
}

#[allow(unused)]
pub fn uint_n_pre_matrix_prod(ctx: &ContextRef, m: &NatType, d: DomainType, rows: &Value, cols: &Value) -> Value {
    let rows = get_varray(rows);
    let cols = get_varray(cols);
    let nr = rows.len();
    let mut xss: Vec<Value> = Vec::with_capacity(nr);
    if m.modulus.as_ref() == Some(&(BigInt::from(340282366920938463463374607431768211455u128) + 1)) {
        uint_n_pre_matrix_prod_helper(d, rows, cols, 0, get_varray_u128, rep::ArrayU128::new, scalar_prod_helper_u128, &mut xss);
    } else if m.modulus.as_ref() == Some(&BigInt::from(18446744073709551616u128)) {
        uint_n_pre_matrix_prod_helper(d, rows, cols, 0, get_varray_u64, rep::ArrayU64::new, scalar_prod_helper_u64, &mut xss);
    } else if m.modulus.as_ref() == Some(&BigInt::from(4294967296u64)) {
        uint_n_pre_matrix_prod_helper(d, rows, cols, 0, get_varray_u32, rep::ArrayU32::new, scalar_prod_helper_u32, &mut xss);
    } else if m.modulus.as_ref() == Some(&BigInt::from(65536u64)) {
        uint_n_pre_matrix_prod_helper(d, rows, cols, 0, get_varray_u16, rep::ArrayU16::new, scalar_prod_helper_u16, &mut xss);
    } else if m.modulus.as_ref() == Some(&BigInt::from(256u64)) {
        uint_n_pre_matrix_prod_helper(d, rows, cols, 0, get_varray_u8, rep::ArrayU8::new, scalar_prod_helper_u8, &mut xss);
    } else {
        let nc = cols.len();
        if d <= CURR_DOMAIN {
            let rows: Vec<Vec<BigInt>> = rows.iter().map(|row| {
                let row = get_varray(row);
                row.iter().map(|x| (m.to_bigint)(x)).collect()
            }).collect();
            let cols: Vec<Vec<BigInt>> = cols.iter().map(|col| {
                let col = get_varray(col);
                col.iter().map(|x| (m.to_bigint)(x)).collect()
            }).collect();
            let nk = rows[0].len();
            for i in 0 .. nr {
                assert!(rows[i].len() == nk);
            }
            for i in 0 .. nc {
                assert!(cols[i].len() == nk);
            }
            for i in 0 .. nr {
                let mut xs: Vec<Value> = Vec::with_capacity(nc);
                for j in 0 .. nc {
                    let mut s = BigInt::zero();
                    for k in 0 .. nk {
                        s = s + &rows[i][k] * &cols[j][k];
                    }
                    xs.push((m.from_bigint)(&s));
                }
                xss.push(rep::Array::new(xs));
            }
        } else {
            for i in 0 .. nr {
                let mut xs: Vec<Value> = Vec::with_capacity(nc);
                xs.resize(nc, ctx.unknown.clone());
                xss.push(rep::Array::new(xs));
            }
        }
    }
    rep::Array::new(xss)
}

#[allow(unused)]
pub fn __add(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, ys: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let (wr_ys, ys_pre) = match get_vpostsoa(ys) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let n = wr_xs.length();
    assert!(wr_ys.length() == n, "__add: argument vectors must have the same length");
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "add", vec![], m, vec![n], vec![wr_xs, wr_ys]);
    let mut rs = Vec::new();
    for i in 0 .. n {
        let x = &xs_pre[i];
        let y = &ys_pre[i];
        let r = if is_unknown(x) || is_unknown(y) {
            ctx.unknown.clone()
        } else {
            (m.add)(x, y)
        };
        rs.push(r);
    }
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), rs)))
}

#[allow(unused)]
pub fn __mul(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, ys: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let (wr_ys, ys_pre) = match get_vpostsoa(ys) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let n = wr_xs.length();
    assert!(wr_ys.length() == n, "__mul: argument vectors must have the same length");
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "mul", vec![], m, vec![n], vec![wr_xs, wr_ys]);
    let mut rs = Vec::new();
    for i in 0 .. n {
        let x = &xs_pre[i];
        let y = &ys_pre[i];
        let r = if is_unknown(x) || is_unknown(y) {
            ctx.unknown.clone()
        } else {
            (m.mul)(x, y)
        };
        rs.push(r);
    }
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), rs)))
}

#[allow(unused)]
pub fn __addc(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, y: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let y_str = &(m.to_bigint)(y).to_string();
    let n = wr_xs.length();
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "addc", vec![y_str], m, vec![n], vec![wr_xs]);
    let mut rs = Vec::new();
    for i in 0 .. n {
        let x = &xs_pre[i];
        let r = if is_unknown(x) {
            ctx.unknown.clone()
        } else {
            (m.add)(x, y)
        };
        rs.push(r);
    }
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), rs)))
}

#[allow(unused)]
pub fn __mulc(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, y: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let y_str = &(m.to_bigint)(y).to_string();
    let n = wr_xs.length();
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "mulc", vec![y_str], m, vec![n], vec![wr_xs]);
    let mut rs = Vec::new();
    for i in 0 .. n {
        let x = &xs_pre[i];
        let r = if is_unknown(x) {
            ctx.unknown.clone()
        } else {
            (m.mul)(x, y)
        };
        rs.push(r);
    }
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), rs)))
}

#[allow(unused)]
pub fn __add_scalar(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, y: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let y_pre = get_pre_value_from_post(y);
    let wr_y = &wire_to_wr(&get_or_create_wire(m, y));
    let n = wr_xs.length();
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "add_scalar", vec![], m, vec![n], vec![wr_xs, wr_y]);
    let mut rs = Vec::new();
    for i in 0 .. n {
        let x = &xs_pre[i];
        let r = if is_unknown(x) || is_unknown(y_pre) {
            ctx.unknown.clone()
        } else {
            (m.add)(x, y_pre)
        };
        rs.push(r);
    }
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), rs)))
}

#[allow(unused)]
pub fn __mul_scalar(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, y: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let y_pre = get_pre_value_from_post(y);
    let wr_y = &wire_to_wr(&get_or_create_wire(m, y));
    let n = wr_xs.length();
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "mul_scalar", vec![], m, vec![n], vec![wr_xs, wr_y]);
    let mut rs = Vec::new();
    for i in 0 .. n {
        let x = &xs_pre[i];
        let r = if is_unknown(x) || is_unknown(y_pre) {
            ctx.unknown.clone()
        } else {
            (m.mul)(x, y_pre)
        };
        rs.push(r);
    }
    rep::PostSoA::new(SoA::Scalar((output_wrs[0].clone(), rs)))
}

#[allow(unused)]
pub fn __sum(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let n = wr_xs.length();
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "sum", vec![], m, vec![1], vec![wr_xs]);
    let mut s = ctx.integer_zero.clone();
    let mut u = false;
    for i in 0 .. n {
        let x = &xs_pre[i];
        let r = if is_unknown(x) {
            u = true;
            break;
        } else {
            let x = (m.to_bigint)(x);
            s = s + x;
        };
    }
    let r = if u {
        ctx.unknown.clone()
    } else {
        (m.from_bigint)(&s)
    };
    let w = output_wrs[0].index(0);
    rep::Post::new(w, r)
}

#[allow(unused)]
pub fn __prod(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let n = wr_xs.length();
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "product", vec![], m, vec![1], vec![wr_xs]);
    let mut s = ctx.integer_one.clone();
    let mut u = false;
    for i in 0 .. n {
        let x = &xs_pre[i];
        let r = if is_unknown(x) {
            u = true;
            break;
        } else {
            let x = (m.to_bigint)(x);
            s = s * x;
        };
    }
    let r = if u {
        ctx.unknown.clone()
    } else {
        (m.from_bigint)(&s)
    };
    let w = output_wrs[0].index(0);
    rep::Post::new(w, r)
}

#[allow(unused)]
pub fn __dotprod(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, ys: &Value) -> Value {
    let (wr_xs, xs_pre) = match get_vpostsoa(xs) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let (wr_ys, ys_pre) = match get_vpostsoa(ys) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let n = wr_xs.length();
    assert!(wr_ys.length() == n, "__dotprod: argument vectors must have the same length");
    let output_wrs = sieve_backend().plugin_apply_wr("vectors_v1", "dotproduct", vec![], m, vec![1], vec![wr_xs, wr_ys]);
    let mut s = ctx.integer_zero.clone();
    let mut u = false;
    for i in 0 .. n {
        let x = &xs_pre[i];
        let y = &ys_pre[i];
        let r = if is_unknown(x) || is_unknown(y) {
            u = true;
            break;
        } else {
            let x = (m.to_bigint)(x);
            let y = (m.to_bigint)(y);
            s = s + x * y;
        };
    }
    let r = if u {
        ctx.unknown.clone()
    } else {
        (m.from_bigint)(&s)
    };
    let w = output_wrs[0].index(0);
    rep::Post::new(w, r)
}

#[allow(unused)]
pub fn __assert_perm(ctx: &ContextRef, m: &NatType, d: DomainType, xs: &Value, ys: &Value) {
    let (xs_full, xs_ir) = get_slice(xs.clone());
    let (ys_full, ys_ir) = get_slice(ys.clone());
    let (wr_xs_full, xs_pre_full) = match get_vpostsoa(&xs_full) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let (wr_ys_full, ys_pre_full) = match get_vpostsoa(&ys_full) {
        SoA::Scalar(t) => t,
        _ => panic!(),
    };
    let wr_xs = wr_xs_full.slice(&xs_ir);
    let wr_ys = wr_ys_full.slice(&ys_ir);
    let n = wr_xs.length();
    assert!(wr_ys.length() == n, "__assert_perm: argument vectors must have the same length");
    let dim = match xs.view() {
        ValueView::Tensor(_, dim) => dim.clone(),
        _ => vec![n],
    };
    let dim_ys = match ys.view() {
        ValueView::Tensor(_, dim) => dim.clone(),
        _ => vec![n],
    };
    assert!(dim == dim_ys, "__assert_perm: argument tensors must have the same size");
    assert!(dim.len() >= 1);
    let tuple_len: usize = dim[1..].iter().product(); // the length of the (dim.len()-1)-dimensional subtensors, the list of which is permuted to transform xs into ys
    let output_wrs = sieve_backend().plugin_apply_wr("permutation_check_v1", "assert_perm", vec![&tuple_len.to_string()], m, vec![], vec![&wr_xs, &wr_ys]);
    if tuple_len == 1 { // slightly faster version for 1-dimensional vectors
        let mut u = false;
        let mut xv = Vec::new();
        let mut yv = Vec::new();
        let xs_pre = &xs_pre_full[xs_ir.first .. xs_ir.first + xs_ir.length];
        let ys_pre = &ys_pre_full[ys_ir.first .. ys_ir.first + ys_ir.length];
        for (x, y) in xs_pre.iter().zip(ys_pre.iter()) {
            let r = if is_unknown(x) || is_unknown(y) {
                u = true;
                break;
            } else {
                let x = (m.to_bigint)(x);
                let y = (m.to_bigint)(y);
                xv.push(x);
                yv.push(y);
            };
        }
        if !u {
            xv.sort();
            yv.sort();
            assert!(xv == yv, "__assert_perm: argument vectors are not permutations of each other");
        }
    } else { // general version
        let mut u = false;
        let mut xv = Vec::new();
        let mut yv = Vec::new();
        let mut xt = Vec::new();
        let mut yt = Vec::new();
        let xs_pre = &xs_pre_full[xs_ir.first .. xs_ir.first + xs_ir.length];
        let ys_pre = &ys_pre_full[ys_ir.first .. ys_ir.first + ys_ir.length];
        for (x, y) in xs_pre.iter().zip(ys_pre.iter()) {
            let r = if is_unknown(x) || is_unknown(y) {
                u = true;
                break;
            } else {
                let x = (m.to_bigint)(x);
                let y = (m.to_bigint)(y);
                xt.push(x);
                yt.push(y);
                if xt.len() >= tuple_len {
                    xv.push(xt);
                    xt = Vec::new();
                    yv.push(yt);
                    yt = Vec::new();
                }
            };
        }
        if !u {
            xv.sort();
            yv.sort();
            assert!(xv == yv, "__assert_perm: argument tensors are not permutations of each other");
        }
    }
}

// inputs are the SIEVE wire numbers of inputs
// the return value is the SIEVE wire numbers of outputs
pub fn circuit_to_sieve(ctx: &ContextRef, m: &NatType, c: &Circuit, inputs: Vec<Vec<Wire>>) -> Vec<Vec<Wire>> {

    let mut arr = Vec::new();
    arr.resize_with(c.num_wires, || {sieve_zero_wire(ctx,m)});

    assert!(c.input_wires.len() == inputs.len(), "Invalid number of inputs to circuit call");
    for i in 0 .. inputs.len() {
        assert!(c.input_wires[i].len() == inputs[i].len(), "Invalid length of an input in circuit call");
        for j in 0 .. inputs[i].len() {
            arr[c.input_wires[i][j]] = sieve_clone_wire(ctx,m,&inputs[i][j]);
        }
    }
    use Gate::*;
    if is_nat_boolean(m) {
        for g in &c.gates {
            match g {
                And(x, y, z) => {
                    arr[*x] = sieve_and(ctx, m, &arr[*y], &arr[*z]);
                }
                Xor(x, y, z) => {
                    arr[*x] = sieve_xor(ctx, m, &arr[*y], &arr[*z]);
                }
                Not(x, y) => {
                    arr[*x] = sieve_not(ctx, m, &arr[*y]);
                }
                CopyWire(x, y) => {
                    arr[*x] = sieve_copy_bool(ctx, m, &arr[*y]);
                }
            }
        }
    } else {
        let m_minus_1 = match m.modulus {
            Some(ref m) => m - 1,
            _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
        };
        let m_minus_2 = match m.modulus {
            Some(ref m) => m - 2,
            _ => zksc_panic!(ctx, "Infinite modulus not supported in $post"),
        };
        for g in &c.gates {
            match g {
                And(x, y, z) => {
                    arr[*x] = sieve_mul(ctx, m, &arr[*y], &arr[*z]);
                }
                Xor(x, y, z) => {
                    let w1 = &arr[*y];
                    let w2 = &arr[*z];
                    let x_plus_y = sieve_add(ctx, m, w1, w2);
                    let x_times_y = sieve_mul(ctx, m, w1, w2);
                    let minus2_x_times_y = sieve_mulc(ctx, m, &x_times_y, &m_minus_2);
                    let w = sieve_add(ctx, m, &x_plus_y, &minus2_x_times_y);
                    arr[*x] = w;
                }
                Not(x, y) => {
                    let w1 = &arr[*y];
                    let minus_x = sieve_mulc(ctx, m, w1, &m_minus_1);
                    let w = sieve_addc(ctx, m, &minus_x, &ctx.integer_one);
                    arr[*x] = w;
                }
                CopyWire(x, y) => {
                    arr[*x] = sieve_clone_wire(ctx, m, &arr[*y]);
                }
            }
        }
    }
    let mut outputs = Vec::new();
    for i in 0 .. c.output_wires.len() {
        let mut output = Vec::new();
        for j in 0 .. c.output_wires[i].len() {
            output.push(sieve_clone_wire(ctx,m,&arr[c.output_wires[i][j]]));
        }
        outputs.push(output);
    }
    outputs
}

#[allow(unused)]
pub fn call(ctx: &ContextRef, m: &NatType, s: StageType, d: DomainType, circuit_name: &Value, inputs: &Value) -> Value {

    let circuit_name = get_vstr(circuit_name);
    let circuit = &*((ctx.circuit_loader.borrow_mut())(String::from(circuit_name))
        .unwrap_or_else(|| panic!("Circuit '{}' not found", circuit_name)));
    let output_values = if d <= CURR_DOMAIN {
        let input_values = get_varray(inputs).iter().map(|x| get_varray(x).iter().map(|x| *get_vbool(x)).collect()).collect();
        eval_circuit(circuit, input_values).iter().map(
            |xs| xs.iter().map(
                |x| rep::Bool::new(*x)
            ).collect()
        ).collect()
    } else {
        get_unknown_outputs_for_circuit(circuit)
    };
    let outputs = match s {
        Pre => rep::Array::new(output_values.iter().map(
            |x| rep::Array::new(x.iter().map(
                |x| x.clone()
            ).collect())
        ).collect()),
        Post => {
            let input_wires = get_varray(inputs).iter().map(
                |x| get_varray(x).iter().map(
                    |x| get_or_create_bool2_wire(ctx, m, x)
                ).collect()
            ).collect();
            let output_wires = circuit_to_sieve(ctx, m, circuit, input_wires);
            rep::Array::new(output_values.iter().zip(output_wires.iter()).map(
                |(x,w)| rep::Array::new(x.iter().zip(w.iter()).map(
                    |(x,w)| rep::Post::new(sieve_clone_wire(ctx,m,w), x.clone())
                ).collect())
            ).collect())
        }
    };
    outputs
}

#[allow(unused)]
pub fn sieve_define_function(ctx: &ContextRef, stack: &mut Stack, fname: &String, f: FnHOF,
                            ts: &Vec<TypeEnum>, output_moduli: &Vec<&NatType>, env_moduli: &Vec<SoA<(NatType, bool)>>,
                            env_values: &Vec<Value>,
                            input_moduli: &Vec<SoA<&NatType>>) -> usize {
    let env_values: Vec<SoA<Value>> = env_values.iter().map(|v| sized_value_to_soa(v)).collect();
    let list_lengths: Vec<Vec<usize>> = env_values.iter().map(|soa| soa.get_list_lengths()).collect();
    let env_pre: Vec<SoA<(Option<Value>, Option<Integer>)>> = env_moduli.iter().zip(env_values.into_iter()).map(|(soa_m, soa_v)| {
        soa_m.clone().zip(soa_v).map(&|((m, is_pre_public), v)| {
            if is_pre_public {
                let x = get_pre_or_post_uint_or_bool(ctx, &m, &v);
                (Some(v), Some(x))
            } else {
                (None, None)
            }
        })
    }).collect();
    let mut pre_public_params: Vec<Integer> = Vec::new();
    for soa in &env_pre {
        for (_, x) in soa.flatten() {
            match x {
                Some(x) => pre_public_params.push(x.clone()),
                None => {}
            }
        }
    }
    let env_pre: Vec<SoA<Option<Value>>> = env_pre.into_iter().map(|soa| soa.map(&|(x, _)| x)).collect();
    // TODO: the cloning may be a bit inefficient if there are large moduli (we actually only need the tags)
    // TODO: add $pre @public parameters to the hash
    let hash_params = (fname.clone(), ts.clone(), pre_public_params, list_lengths);
    // need to save the result to a variable, otherwise it gets BorrowMutError
    let r = ctx.sieve_functions.borrow().get(&hash_params).cloned();
    match r {
        Some(uid) => uid,
        None => {
            let mut all_input_moduli = Vec::with_capacity(env_moduli.len() + input_moduli.len());
            for soa in env_moduli {
                for (m, is_pre_public) in soa.flatten() {
                    if !is_pre_public {
                        all_input_moduli.push(m);
                    }
                }
            }
            for soa in input_moduli {
                for m in soa.flatten() {
                    all_input_moduli.push(m);
                }
            }
            let env_post: Vec<SoA<Option<()>>> = env_moduli.iter().map(|soa| soa.map_ref(&|(m, is_pre_public)| {
                if *is_pre_public {
                    None
                } else {
                    Some(())
                }
            })).collect();
            let (input_wires, uid) = sieve_backend().begin_function(fname, output_moduli, all_input_moduli);
            let input_scalars: Vec<_> = input_wires.into_iter().map(|w| rep::Post::new(w, ctx.unknown.clone())).collect();
            let mut i: usize = 0;
            let mut input_values: Vec<_> = env_post.into_iter().zip(env_pre.into_iter()).map(|(soa_post, soa_pre)| soa_to_value(combine_soa_options(soa_pre, unflatten_soa_option(&soa_post, &input_scalars, &mut i)))).collect();
            let mut input_values2 = input_moduli.iter().map(|soa| soa_to_value(soa.unflatten(&input_scalars, &mut i))).collect();
            input_values.append(&mut input_values2);
            if input_values.is_empty() {
                input_values.push(ctx.scalar.clone());
            }
            *ctx.is_inside_sieve_fn_def.borrow_mut() = true;
            *ctx.sieve_fn_witness_count.borrow_mut() = 0;
            let output_value = f(ctx, stack, ts, &input_values);
            // now *ctx.sieve_fn_witness_count.borrow() contains the number of witness values in the current sieve function
            *ctx.is_inside_sieve_fn_def.borrow_mut() = false;
            let tuple_wocs = get_tuple_wires(ctx, output_moduli, &output_value);
            sieve_backend().end_function(tuple_wocs);
            ctx.sieve_functions.borrow_mut().insert(hash_params, uid);
            uid
        }
    }
}

fn get_slice(v: Value) -> (Value, IndexRange) {
    match v.view() {
        ValueView::Slice(v, ir) => (v.clone(), ir.clone()),
        // TODO: it should be possible to use v instead of the following two v.clone()'s but it would require ugly code to end the v.view() borrow before the v.clone()
        ValueView::Array(arr) => (v.clone(), IndexRange { first: 0, length: arr.len() }),
        ValueView::PostSoA(soa) => (v.clone(), IndexRange { first: 0, length: post_soa_length(soa) }),
        ValueView::Tensor(arr, _) => get_slice(arr.clone()),
        _ => panic!("get_slices can only be applied to lists, arrays, tensors, and slices"),
    }
}

fn get_slices(vs: Vec<Value>) -> (Vec<Value>, Vec<IndexRange>) {
    vs.into_iter().map(|v| { get_slice(v) }).unzip()
}

fn check_dims_equal(vs: &Vec<Value>) -> Vec<usize> {
    let mut has_curr_dim = false;
    let mut curr_dim: Vec<usize> = Vec::new();
    vs.iter().for_each(|v| {
        let dim =
            match v.view() {
                ValueView::Slice(_, ir) => vec![ir.length],
                ValueView::Array(arr) => vec![arr.len()],
                ValueView::PostSoA(soa) => vec![post_soa_length(soa)],
                ValueView::Tensor(_, dim) => dim.clone(),
                _ => panic!("check_dims_equal can only be applied to lists, arrays, tensors, and slices"),
            };
        if has_curr_dim {
            if dim != curr_dim {
                panic!("Tensor arguments of vectorized application or zip with must have the same size");
            }
        } else {
            curr_dim = dim;
            has_curr_dim = true;
        }
    });
    curr_dim
}

fn zip_pre_helper(ctx: &ContextRef, stack: &mut Stack, ts: &Vec<TypeEnum>,
                  arrs: Vec<&Vec<Value>>, irs: &Vec<IndexRange>, f: FnHOF) -> Vec<Value> {
    let n = irs[0].length;
    let mut res: Vec<Value> = Vec::with_capacity(n);
    for i in 0 .. n {
        let args: Vec<Value> = arrs.iter().zip(irs.iter()).map(|(arr, ir)| arr[ir.index(i)].clone()).collect();
        res.push(f(ctx, stack, ts, &args));
    }
    res
}

fn zip_soa_pre_helper(ctx: &ContextRef, stack: &mut Stack, ts: &Vec<TypeEnum>,
                      soas: &Vec<&SoA<(WireRange, Vec<Value>)>>, irs: &Vec<IndexRange>, f: FnHOF) -> Vec<Value> {
    let n = irs[0].length;
    let mut res: Vec<Value> = Vec::with_capacity(n);
    *ctx.is_inside_sieve_fn_call.borrow_mut() = true;
    for i in 0 .. n {
        let args: Vec<Value> = soas.iter().zip(irs.iter()).map(|(soa, ir)| post_soa_index_to_pre(soa, ir.index(i))).collect();
        let y = f(ctx, stack, ts, &args);
        if i == 0 && is_unknown(&y) {
            // To make it faster, we use only one unknown element, this is checked for elsewhere
            //res.resize(n, ctx.unknown.clone());
            res.resize(1, ctx.unknown.clone());
            break;
        }
        res.push(y);
    }
    *ctx.is_inside_sieve_fn_call.borrow_mut() = false;
    res
}

fn zip_hof_pre_helper(ctx: &ContextRef, stack: &mut Stack, ts: &Vec<TypeEnum>, args_env: Vec<Value>,
                      arrs: Vec<&Vec<Value>>, irs: &Vec<IndexRange>, f: FnHOF) -> Vec<Value> {
    let n = irs[0].length;
    let mut res: Vec<Value> = Vec::with_capacity(n);
    for i in 0 .. n {
        let mut args2: Vec<Value> = arrs.iter().zip(irs.iter()).map(|(arr, ir)| arr[ir.index(i)].clone()).collect();
        let mut args = args_env.clone();
        args.append(&mut args2);
        res.push(f(ctx, stack, ts, &args));
    }
    res
}

fn zip_hof_soa_pre_helper(ctx: &ContextRef, stack: &mut Stack, ts: &Vec<TypeEnum>, args_env: Vec<Value>,
                          soas: &Vec<&SoA<(WireRange, Vec<Value>)>>, irs: &Vec<IndexRange>, f: FnHOF) -> Vec<Value> {
    let n = irs[0].length;
    let mut res: Vec<Value> = Vec::with_capacity(n);
    *ctx.is_inside_sieve_fn_call.borrow_mut() = true;
    for i in 0 .. n {
        let mut args2: Vec<Value> = soas.iter().zip(irs.iter()).map(|(soa, ir)| post_soa_index_to_pre(soa, ir.index(i))).collect();
        let mut args = args_env.clone();
        args.append(&mut args2);
        let y = f(ctx, stack, ts, &args);
        if i == 0 && is_unknown(&y) {
            // To make it faster, we use only one unknown element, this is checked for elsewhere
            //res.resize(n, ctx.unknown.clone());
            res.resize(1, ctx.unknown.clone());
            break;
        }
        res.push(y);
    }
    *ctx.is_inside_sieve_fn_call.borrow_mut() = false;
    res
}

fn zip_post_soa_helper(ctx: &ContextRef, stack: &mut Stack, fname: &String, f: FnHOF,
                   ts: &Vec<TypeEnum>, output_moduli: SoA<&NatType>, env_moduli: &Vec<SoA<(NatType, bool)>>,
                   env_values: &Vec<Value>,
                   input_moduli: Vec<SoA<&NatType>>, env_wires: Vec<&Wire>,
                   irs: &Vec<IndexRange>, soas: Vec<&SoA<(WireRange, Vec<Value>)>>, output_values: Vec<Value>) -> Value {
    if irs[0].length == 0 {
        return rep::PostSoA::new(SoA::Empty);
    }
    let output_moduli_flattened = output_moduli.flatten().into_iter().cloned().collect();
    let unique_fname = sieve_define_function(ctx, stack, fname, f, ts, &output_moduli_flattened, env_moduli, env_values, &input_moduli);
    let wrs: Vec<Vec<WireRange>> = soas.iter().zip(irs.iter()).map(|(soa, ir)|
        soa.flatten().iter().map(|(wr, _)| wr.slice(ir)).collect()
    ).collect();
    let wrs = wrs.concat();
    let wrs: Vec<&WireRange> = wrs.iter().collect();
    let input_moduli: Vec<Vec<_>> = input_moduli.iter().map(|soa| soa.flatten().into_iter().cloned().collect()).collect();
    let input_moduli = input_moduli.concat();
    let mut env_moduli_flattened = Vec::with_capacity(env_moduli.len());
    for soa in env_moduli {
        for (m, is_pre_public) in soa.flatten() {
            if !is_pre_public {
                env_moduli_flattened.push(m.clone());
            }
        }
    }
    let output_wrs = sieve_backend().vectorized_apply(unique_fname, output_moduli_flattened, input_moduli, &env_moduli_flattened, env_wires, wrs);
    let output_wr_soa = output_moduli.unflatten_from_start(&output_wrs);
    let output_value_soa = aos_to_soa(&output_values);
    rep::PostSoA::new(output_wr_soa.zip(output_value_soa))
}

fn call_sieve_post_soa_helper(
        ctx: &ContextRef, stack: &mut Stack, fname: &String, f: FnHOF,
        ts: &Vec<TypeEnum>, output_moduli: SoA<&NatType>,
        input_moduli: Vec<SoA<(&NatType, bool)>>,
        input_values: &Vec<Value>,
        soas: Vec<SoA<Value>>, output_value: Value
) -> Value {
    let input_moduli2: Vec<_> = input_moduli.iter().map(|soa| soa.map_ref(&|(m, is_pre_public)| ((*m).clone(), *is_pre_public))).collect();
    let output_moduli_flattened = output_moduli.flatten().into_iter().cloned().collect();
    let unique_fname = sieve_define_function(ctx, stack, fname, f, ts, &output_moduli_flattened, &input_moduli2, input_values, &vec![]);

    let mut wires: Vec<Wire> = Vec::new();
    soas.into_iter().zip(input_moduli.into_iter()).for_each(|(soa_v, soa_m)| {
        soa_v.zip(soa_m).flatten().into_iter().for_each(|(v, (m, is_pre_public))| {
            if !is_pre_public {
                wires.push(get_or_create_wire(m, v));
            }
        })
    });
    let mut all_input_wires = Vec::with_capacity(wires.len());
    for w in &wires {
        all_input_wires.push(w);
    }

    let output_wires = sieve_backend().apply(unique_fname, output_moduli_flattened, all_input_wires);
    let output_wire_soa = output_moduli.unflatten_from_start(&output_wires);
    let output_value_soa = sized_value_to_soa(&output_value);
    soa_to_value(output_wire_soa.zip(output_value_soa).map(&|(w, v)| rep::Post::new(w, v)))
}

fn match_sieve_post_soa_helper(
        ctx: &ContextRef, stack: &mut Stack, fs: Vec<&HOF>,
        ts: &Vec<TypeEnum>,
        ints: Vec<Integer>,
        x: &Value, x_modulus: &NatType,
        output_moduli: SoA<&NatType>,
        input_moduli: Vec<SoA<(&NatType, bool)>>,
        input_values: &Vec<Value>,
        soas: Vec<SoA<Value>>, output_value: Value,
        chosen_branch: Option<usize>,
) -> Value {
    let input_moduli2: Vec<_> = input_moduli.iter().map(|soa| soa.map_ref(&|(m, is_pre_public)| ((*m).clone(), *is_pre_public))).collect();
    let output_moduli_flattened: Vec<_> = output_moduli.flatten().into_iter().cloned().collect();
    let mut unique_fnames: Vec<usize> = Vec::new();
    let mut witness_counts: Vec<u64> = Vec::new();
    let mut max_witness_count: u64 = 0;
    for f in fs {
        let unique_fname = sieve_define_function(ctx, stack, &f.name.to_string(), f.f, ts, &output_moduli_flattened, &input_moduli2, input_values, &vec![]);
        unique_fnames.push(unique_fname);
        witness_counts.push(*ctx.sieve_fn_witness_count.borrow());
    }
    for x in &witness_counts {
        if *x > max_witness_count {
            max_witness_count = *x;
        }
    }
    match chosen_branch {
        None => {}
        Some(chosen_branch) => {
            let num_witness_values_to_pad = max_witness_count - witness_counts[chosen_branch];
            if num_witness_values_to_pad > 0 {
                let m = output_moduli_flattened[0];
                let zero = (m.from_bigint)(&ctx.integer_zero);
                for _ in 0 .. num_witness_values_to_pad {
                    sieve_backend().add_witness(m, &zero);
                }
            }
        }
    }

    let mut wires: Vec<Wire> = Vec::new();
    soas.into_iter().zip(input_moduli.into_iter()).for_each(|(soa_v, soa_m)| {
        soa_v.zip(soa_m).flatten().into_iter().for_each(|(v, (m, is_pre_public))| {
            if !is_pre_public {
                wires.push(get_or_create_wire(m, v));
            }
        })
    });
    let mut all_input_wires = Vec::with_capacity(wires.len());
    for w in &wires {
        all_input_wires.push(w);
    }

    let mut input_moduli_flattened = Vec::with_capacity(input_moduli2.len());
    for soa in input_moduli2 {
        for (m, is_pre_public) in soa.flatten() {
            if !is_pre_public {
                input_moduli_flattened.push(m.clone());
            }
        }
    }

    let x_wire = get_or_create_wire(x_modulus, x);
    let default_unique_fname = unique_fnames[0];
    let other_unique_fnames = unique_fnames[1..].to_vec();
    let output_wires = sieve_backend().switch_apply(&other_unique_fnames, default_unique_fname, &ints, x_modulus,
                                output_moduli_flattened, input_moduli_flattened.iter().collect(), &x_wire, all_input_wires,
                                max_witness_count);
    let output_wire_soa = output_moduli.unflatten_from_start(&output_wires);
    let output_value_soa = sized_value_to_soa(&output_value);
    soa_to_value(output_wire_soa.zip(output_value_soa).map(&|(w, v)| rep::Post::new(w, v)))
}

#[allow(unused)]
pub fn call_sieve(ctx: &ContextRef, stack: &mut Stack, moduli: (SoA<&NatType>, Vec<SoA<(&NatType, bool)>>),
                  ts: Vec<TypeEnum>, vs: Vec<Value>, sieve_fn: String, f: FnHOF) -> Value {
    let (output_moduli, input_moduli) = moduli;
    let soas: Vec<SoA<Value>> = vs.iter().map(|v| sized_value_to_soa(v)).collect();
    let input_moduli: Vec<_> = input_moduli.iter().zip(soas.iter()).map(|(soa1, soa2)| soa1.expand_listtype(soa2)).collect();
    let vs_pre: Vec<Value> = soas.iter().map(|soa| soa_to_value(soa.map_ref(&|v| get_pre_value_from_post(v).clone()))).collect();
    *ctx.is_inside_sieve_fn_call.borrow_mut() = true;
    let res = f(ctx, stack, &ts, &vs_pre);
    *ctx.is_inside_sieve_fn_call.borrow_mut() = false;
    let output_moduli = output_moduli.expand_listtype(&sized_value_to_soa(&res));
    call_sieve_post_soa_helper(ctx, stack, &sieve_fn, f, &ts, output_moduli, input_moduli, &vs, soas, res)
}

#[allow(unused)]
pub fn match_sieve(ctx: &ContextRef, stack: &mut Stack, x: &Value, x_modulus: &NatType, ints: Vec<Integer>, moduli: (SoA<&NatType>, Vec<SoA<(&NatType, bool)>>),
                  vs: Vec<Value>, fnames: Vec<String>, fs: Vec<&Value>) -> Value {
    let (output_moduli, input_moduli) = moduli;
    let soas: Vec<SoA<Value>> = vs.iter().map(|v| sized_value_to_soa(v)).collect();
    let input_moduli: Vec<_> = input_moduli.iter().zip(soas.iter()).map(|(soa1, soa2)| soa1.expand_listtype(soa2)).collect();
    let vs_pre: Vec<Value> = if vs.is_empty() {
        vec![ctx.scalar.clone()]
    } else {
        soas.iter().map(|soa| soa_to_value(soa.map_ref(&|v| get_pre_value_from_post(v).clone()))).collect()
    };
    let fs: Vec<&HOF> = fs.into_iter().map(|f| get_vfun(f)).collect();
    let ts = vec![];
    *ctx.is_inside_sieve_fn_call.borrow_mut() = true;
    let mut res: Option<Value> = None;
    let mut chosen_branch: Option<usize> = None;
    if is_unknown(x) {
        res = Some(ctx.unknown.clone());
    } else {
        let x_int = get_pre_or_post_uint(x_modulus, x);
        for i in 0 .. ints.len() {
            if x_int == ints[i] {
                res = Some((fs[i + 1].f)(ctx, stack, &ts, &vs_pre));
                chosen_branch = Some(i + 1);
                break;
            }
        }
        if res.is_none() {
            res = Some((fs[0].f)(ctx, stack, &ts, &vs_pre));
            chosen_branch = Some(0);
        }
    }
    let res = res.unwrap();
    *ctx.is_inside_sieve_fn_call.borrow_mut() = false;
    match_sieve_post_soa_helper(ctx, stack, fs, &ts, ints, x, x_modulus, output_moduli, input_moduli, &vs, soas, res, chosen_branch)
}

fn create_tensor_if_needed(v: Value, dim: Vec<usize>) -> Value {
    if dim.len() == 1 {
        v
    } else {
        rep::Tensor::new(v, dim)
    }
}

#[allow(unused)]
pub fn zip(ctx: &ContextRef, stack: &mut Stack, moduli: (SoA<&NatType>, Vec<SoA<&NatType>>),
           ts: Vec<TypeEnum>, vs: Vec<Value>, sieve_fn: Option<String>, f: FnHOF) -> Value {
    let (output_moduli, input_moduli) = moduli;
    if vs.len() > input_moduli.len() {
        panic!("Functions applied in a vectorized way cannot return functions");
    }
    assert!(vs.len() >= 1);
    for v in &vs {
        if is_unknown(v) {
            return ctx.unknown.clone();
        }
    }
    let tensor_dim = check_dims_equal(&vs);
    let (vs, irs) = get_slices(vs);
    create_tensor_if_needed(
        match vs[0].view() {
            ValueView::Array(_) => {
                let arrs: Vec<&Vec<Value>> = vs.iter().map(|v| get_varray(v)).collect();
                let res = zip_pre_helper(ctx, stack, &ts, arrs, &irs, f);
                rep::Array::new(res)
            }
            ValueView::PostSoA(_) => {
                match sieve_fn {
                    Some(s) => {
                        // compute the result in $pre
                        let soas: Vec<&SoA<(WireRange, Vec<Value>)>> = vs.iter().map(|v| get_vpostsoa(v)).collect();
                        let res = zip_soa_pre_helper(ctx, stack, &ts, &soas, &irs, f);
                        // use the plugin in the circuit
                        zip_post_soa_helper(ctx, stack, &s, f, &ts, output_moduli, &vec![], &vec![], input_moduli, vec![], &irs, soas, res)
                    }
                    None =>
                        panic!("Only SIEVE IR functions can be applied in a vectorized way to $post arrays")
                }
            }
            _ => panic!("zip: not an array"),
        },
        tensor_dim)
}

#[allow(unused)]
pub fn zip_hof(ctx: &ContextRef, stack: &mut Stack, output_moduli: SoA<&NatType>, input_moduli: Vec<SoA<&NatType>>,
               vs: Vec<Value>, f: &Value) -> Value {
    assert!(vs.len() >= 1);
    for v in &vs {
        if is_unknown(v) {
            return ctx.unknown.clone();
        }
    }
    let f = get_vfun(f);
    if vs.len() > f.remaining_value_args {
        panic!("Functions applied in a vectorized way cannot return functions");
    }
    let tensor_dim = check_dims_equal(&vs);
    let (vs, irs) = get_slices(vs);
    create_tensor_if_needed(
        match vs[0].view() {
            ValueView::Array(_) => {
                let arrs: Vec<&Vec<Value>> = vs.iter().map(|v| get_varray(v)).collect();
                let args_env: Vec<Value> = f.value_args.clone();
                let res = zip_hof_pre_helper(ctx, stack, &f.type_args, args_env, arrs, &irs, f.f);
                rep::Array::new(res)
            }
            ValueView::PostSoA(_) => {
                if f.is_sieve {
                    // compute the result in $pre
                    let soas: Vec<&SoA<(WireRange, Vec<Value>)>> = vs.iter().map(|v| get_vpostsoa(v)).collect();
                    let args_env_pre: Vec<Value> = f.value_args.iter().map(|v| get_pre_value_from_post(v).clone()).collect();
                    let res = zip_hof_soa_pre_helper(ctx, stack, &f.type_args, args_env_pre, &soas, &irs, f.f);
                    // use the plugin in the circuit
                    let mut env_wires: Vec<Wire> = Vec::new();
                    f.value_args.iter().zip(f.sieve_env_moduli.iter()).for_each(|(v, soa_m)| {
                        sized_value_to_soa(v).zip(soa_m.clone()).flatten().into_iter().for_each(|(v, (m, is_pre_public))| {
                            if !is_pre_public {
                                env_wires.push(get_or_create_wire(m, v));
                            }
                        })
                    });
                    zip_post_soa_helper(ctx, stack, &f.name.to_string(), f.f, &f.type_args, output_moduli, &f.sieve_env_moduli, &f.value_args, input_moduli, env_wires.iter().collect(), &irs, soas, res)
                } else {
                    panic!("Only SIEVE IR functions can be applied in a vectorized way to $post arrays")
                }
            }
            _ => panic!("zip: not an array"),
        },
        tensor_dim)
}

#[allow(unused)]
pub fn freeze(ctx: &ContextRef, t: &Type, s: StageType, d: DomainType, dl: DomainType, v: &Value) -> Value {
    let contains_pre = t.contains_scalar_with_stage(s, Pre);
    let contains_post = t.contains_scalar_with_stage(s, Post);
    if contains_pre && contains_post {
        panic!("freeze: vectors cannot currently contain both pre and post scalars");
    }
    if contains_post && use_iter_plugin(ctx) && !ctx.inside_sieve_fn_call() {
        let v = unslice_helper(v);
        let aos = get_varray(&v);
        let soa = aos_to_soa(aos);
        let soa = soa_add_moduli_and_domains_and_need_check_bit(t, d, soa);
        let soa = soa.map(&|(m, d, _need_check_bit, xs)| {
            let wocs = xs.iter().map(|x| {
                if is_const_or_pre(x) {
                    WireOrConst::C(get_pre_or_post_uint_or_bool(ctx, m, x))
                } else {
                    WireOrConst::W(get_wire(x))
                }
            }).collect();
            let wr = sieve_backend().create_vector(m, wocs);
            let xs_pre = xs.iter().map(|x| get_pre_value_from_post(x).clone()).collect();
            (wr, xs_pre)
        });
        rep::PostSoA::new(soa)
    } else {
        v.clone()
    }
}

#[allow(unused)]
fn thaw_helper(v: &Value) -> Value {
    let v = unslice_helper(v);
    match v.view() {
        ValueView::PostSoA(soa) => {
            let n = post_soa_length(soa);
            let mut ys = Vec::with_capacity(n);
            for i in 0 .. n {
                ys.push(post_soa_index(soa, i));
            }
            rep::Array::new(ys)
        }
        _ => panic!("thaw: not a $post array"),
    }
}

#[allow(unused)]
pub fn thaw(ctx: &ContextRef, t: &Type, s: StageType, d: DomainType, dl: DomainType, v: &Value) -> Value {
    let contains_pre = t.contains_scalar_with_stage(s, Pre);
    let contains_post = t.contains_scalar_with_stage(s, Post);
    if contains_pre && contains_post {
        panic!("thaw: vectors cannot currently contain both pre and post scalars");
    }
    if contains_post && use_iter_plugin(ctx) && !ctx.inside_sieve_fn_call() {
        thaw_helper(v)
    } else {
        v.clone()
    }
}

#[allow(unused)]
pub fn flatten(ctx: &ContextRef, s: StageType, d: DomainType, dl: DomainType, v: &Value) -> Value {
    if dl > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        match v.view() {
            ValueView::Tensor(v1, _) => v1.clone(),
            _ => v.clone(),
        }
    }
}

#[allow(unused)]
pub fn size(ctx: &ContextRef, s: StageType, d: DomainType, dl: DomainType, v: &Value) -> Value {
    if dl > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        match v.view() {
            ValueView::Tensor(_, dim) => rep::ArrayU64::new(dim.iter().map(|x| *x as u64).collect()),
            _ => rep::ArrayU64::new(vec![length_helper(v) as u64]),
        }
    }
}

#[allow(unused)]
pub fn unflatten(ctx: &ContextRef, s: StageType, d: DomainType, dl: DomainType, v: &Value, dim: &Value) -> Value {
    if dl > CURR_DOMAIN {
        ctx.unknown.clone()
    } else {
        let v = match v.view() {
            ValueView::Tensor(v, _) => v,
            _ => v,
        };
        let num_elems_old = length_helper(v);
        let dim: Vec<usize> =
            match dim.view() {
                ValueView::ArrayU64(dim) => {
                    dim.iter().map(|v| *v as usize).collect()
                }
                ValueView::Array(dim) => {
                    dim.iter().map(|v| value_to_u64(v) as usize).collect()
                }
                _ => panic!("unflatten: dimension is not a list"),
            };
        let mut num_elems_new: usize = 1;
        for n in &dim {
            num_elems_new = num_elems_new.checked_mul(*n).expect("unflatten: overflow");
        };
        assert!(num_elems_new == num_elems_old, "unflatten: cannot convert a vector into tensor with a different number of elements");
        if dim.len() == 1 {
            v.clone()
        } else {
            rep::Tensor::new(v.clone(), dim)
        }
    }
}

#[derive(Clone, Debug)]
pub enum SoA<T> {
    Tuple(Vec<SoA<T>>),
    List(Vec<SoA<T>>),
    ListType(Box<SoA<T>>),
    Scalar(T),
    Empty,
}

impl<T> SoA<T> {
    fn map<T2, F>(self, f: &F) -> SoA<T2>
    where F: Fn(T) -> T2 {
        match self {
            SoA::Empty => SoA::Empty,
            SoA::Scalar(x) => SoA::Scalar(f(x)),
            SoA::Tuple(soas) => {
                // For some reason, this does not work:
                //SoA::Tuple(soas.into_iter().map(|soa| soa.map(f)).collect())
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.map(f))
                }
                SoA::Tuple(soas2)
            }
            SoA::List(soas) => {
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.map(f))
                }
                SoA::List(soas2)
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn map_mut<T2, F>(self, f: &mut F) -> SoA<T2>
    where F: FnMut(T) -> T2 {
        match self {
            SoA::Empty => SoA::Empty,
            SoA::Scalar(x) => SoA::Scalar(f(x)),
            SoA::Tuple(soas) => {
                // For some reason, this does not work:
                //SoA::Tuple(soas.into_iter().map(|soa| soa.map(f)).collect())
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.map_mut(f))
                }
                SoA::Tuple(soas2)
            }
            SoA::List(soas) => {
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.map_mut(f))
                }
                SoA::List(soas2)
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn map_ref<T2, F>(&self, f: &F) -> SoA<T2>
    where F: Fn(&T) -> T2 {
        match self {
            SoA::Empty => SoA::Empty,
            SoA::Scalar(x) => SoA::Scalar(f(x)),
            SoA::Tuple(soas) => {
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.map_ref(f))
                }
                SoA::Tuple(soas2)
            }
            SoA::List(soas) => {
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.map_ref(f))
                }
                SoA::List(soas2)
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn elems_to_ref(&self) -> SoA<&T> {
        match self {
            SoA::Empty => SoA::Empty,
            SoA::Scalar(x) => SoA::Scalar(&x),
            SoA::Tuple(soas) => {
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.elems_to_ref())
                }
                SoA::Tuple(soas2)
            }
            SoA::List(soas) => {
                let mut soas2 = Vec::with_capacity(soas.len());
                for soa in soas {
                    soas2.push(soa.elems_to_ref())
                }
                SoA::List(soas2)
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn zip<T2>(self, soa: SoA<T2>) -> SoA<(T, T2)> {
        match (self, soa) {
            (SoA::Empty, SoA::Empty) => SoA::Empty,
            (SoA::Scalar(x1), SoA::Scalar(x2)) => SoA::Scalar((x1, x2)),
            (SoA::Tuple(soas1), SoA::Tuple(soas2)) => SoA::Tuple(soas1.into_iter().zip(soas2.into_iter()).map(|(soa1, soa2)| soa1.zip(soa2)).collect()),
            (SoA::List(soas1), SoA::List(soas2)) => SoA::List(soas1.into_iter().zip(soas2.into_iter()).map(|(soa1, soa2)| soa1.zip(soa2)).collect()),
            _ => panic!()
        }
    }

    fn expand_listtype<T2>(&self, soa: &SoA<T2>) -> SoA<T> where T: Clone {
        match (self, soa) {
            (SoA::Empty, SoA::Empty) => SoA::Empty,
            (SoA::Scalar(x1), SoA::Scalar(_)) => SoA::Scalar(x1.clone()),
            (SoA::Tuple(soas1), SoA::Tuple(soas2)) => SoA::Tuple(soas1.into_iter().zip(soas2.into_iter()).map(|(soa1, soa2)| soa1.expand_listtype(soa2)).collect()),
            (SoA::List(soas1), SoA::List(soas2)) => SoA::List(soas1.into_iter().zip(soas2.into_iter()).map(|(soa1, soa2)| soa1.expand_listtype(soa2)).collect()),
            (SoA::ListType(soa1), SoA::List(soas2)) => SoA::List(soas2.into_iter().map(|soa2| soa1.expand_listtype(soa2)).collect()),
            _ => panic!()
        }
    }

    fn get_list_lengths(&self) -> Vec<usize> {
        match self {
            SoA::Empty => vec![],
            SoA::Scalar(_) => vec![],
            SoA::Tuple(soas) => {
                let mut res = Vec::new();
                for soa in soas {
                    res.append(&mut soa.get_list_lengths());
                }
                res
            }
            SoA::List(soas) => {
                let mut res = Vec::new();
                res.push(soas.len());
                for soa in soas {
                    res.append(&mut soa.get_list_lengths());
                }
                res
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn flatten(&self) -> Vec<&T> {
        match self {
            SoA::Empty => vec![],
            SoA::Scalar(x) => vec![x],
            SoA::Tuple(soas) => {
                let mut res = Vec::new();
                for soa in soas {
                    res.append(&mut soa.flatten());
                }
                res
            }
            SoA::List(soas) => {
                let mut res = Vec::new();
                for soa in soas {
                    res.append(&mut soa.flatten());
                }
                res
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn unflatten<T2: Clone>(&self, flat: &Vec<T2>, i: &mut usize) -> SoA<T2> {
        match self {
            SoA::Empty => SoA::Empty,
            SoA::Scalar(_) => {
                let r = SoA::Scalar(flat[*i].clone());
                *i = *i + 1;
                r
            }
            SoA::Tuple(soas) => {
                SoA::Tuple(soas.iter().map(|soa|
                    soa.unflatten(flat, i)
                ).collect())
            }
            SoA::List(soas) => {
                SoA::List(soas.iter().map(|soa|
                    soa.unflatten(flat, i)
                ).collect())
            }
            SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
        }
    }

    fn unflatten_from_start<T2: Clone>(&self, flat: &Vec<T2>) -> SoA<T2> {
        let mut i: usize = 0;
        self.unflatten(flat, &mut i)
    }
}

// soa1 and soa2 must have the same structure and each component must be Some in one and None in the other.
// The return value uses the component from the Some.
fn combine_soa_options<T>(soa1: SoA<Option<T>>, soa2: SoA<Option<T>>) -> SoA<T> {
    soa1.zip(soa2).map(&|x| {
        match x {
            (Some(x), None) => x,
            (None, Some(x)) => x,
            _ => panic!("combine_soa_options: exactly one of the Options must be Some"),
        }
    })
}

fn unflatten_soa_option<T, T2: Clone>(soa: &SoA<Option<T>>, flat: &Vec<T2>, i: &mut usize) -> SoA<Option<T2>> {
    match soa {
        SoA::Empty => SoA::Empty,
        SoA::Scalar(None) => SoA::Scalar(None),
        SoA::Scalar(Some(_)) => {
            let r = SoA::Scalar(Some(flat[*i].clone()));
            *i = *i + 1;
            r
        }
        SoA::Tuple(soas) => {
            SoA::Tuple(soas.iter().map(|soa|
                unflatten_soa_option(soa, flat, i)
            ).collect())
        }
        SoA::List(soas) => {
            SoA::List(soas.iter().map(|soa|
                unflatten_soa_option(soa, flat, i)
            ).collect())
        }
        SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
    }
}


// the Values inside soa should be scalars, corresponding to one element of the SoA
fn soa_to_value(soa: SoA<Value>) -> Value {
    match soa {
        SoA::Empty => panic!("soa_to_value must be applied to an element of a SoA"),
        SoA::Scalar(x) => x,
        SoA::Tuple(soas) => {
            if soas.len() > 0 {
                StructInner::new_tuple(soas.into_iter().map(soa_to_value).collect())
            } else {
                rep::Unit::new()
            }
        }
        SoA::List(soas) => rep::Array::new(soas.into_iter().map(soa_to_value).collect()),
        SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
    }
}

fn post_soa_length(soa: &SoA<(WireRange, Vec<Value>)>) -> usize {
    match soa {
        SoA::Empty => 0,
        SoA::Scalar((wr, _xs)) => wr.length(),
        SoA::Tuple(soas) => post_soa_length(&soas[0]),
        SoA::List(soas) => post_soa_length(&soas[0]),
        SoA::ListType(_) => panic!("SoA::ListType must be expanded with expand_listtype before using"),
    }
}

fn post_soa_index_with_unknown(xs: &Vec<Value>, i: usize) -> Value {
    if i < xs.len() {
        xs[i].clone()
    } else if xs.len() > 0 && is_unknown(&xs[0]) {
        xs[0].clone()
    } else {
        panic!("Index out of bounds")
    }
}

fn post_soa_index_to_pre(soa: &SoA<(WireRange, Vec<Value>)>, i: usize) -> Value {
    soa_to_value(soa.map_ref(&|(_wr, xs)| post_soa_index_with_unknown(xs, i)))
}

fn post_soa_index(soa: &SoA<(WireRange, Vec<Value>)>, i: usize) -> Value {
    soa_to_value(soa.map_ref(&|(wr, xs)| rep::Post::new(wr.index(i), post_soa_index_with_unknown(xs, i))))
}

fn aos_to_soa(aos: &Vec<Value>) -> SoA<Vec<Value>> {
    if aos.is_empty() {
        return SoA::Empty;
    }
    match aos[0].view() {
        ValueView::StructValue(tuple) => {
            let n = tuple.fields.len();
            let tuples: Vec<_> = aos.iter().map(|v| get_vstructvalue(v)).collect();
            let mut soa = Vec::with_capacity(n);
            for i in 0 .. n {
                let arr = tuples.iter().map(|tuple| tuple.fields[i].clone()).collect();
                soa.push(aos_to_soa(&arr));
            }
            SoA::Tuple(soa)
        }
        ValueView::Unit() => SoA::Tuple(vec![]),
        _ => SoA::Scalar(aos.clone())
    }
}

fn sized_value_to_soa(v: &Value) -> SoA<Value> {
    match v.view() {
        ValueView::StructValue(tuple) => {
            let n = tuple.fields.len();
            let mut soa = Vec::with_capacity(n);
            for i in 0 .. n {
                soa.push(sized_value_to_soa(&tuple.fields[i]));
            }
            SoA::Tuple(soa)
        }
        ValueView::Array(arr) => {
            let n = arr.len();
            let mut soa = Vec::with_capacity(n);
            for i in 0 .. n {
                soa.push(sized_value_to_soa(&arr[i]));
            }
            SoA::List(soa)
        }
        ValueView::Unit() => SoA::Tuple(vec![]),
        _ => SoA::Scalar(v.clone())
    }
}

fn soa_add_moduli_and_domains_and_need_check_bit<'a>(t: &'a Type<'a>, d: DomainType, soa: SoA<Vec<Value>>) -> SoA<(&'a NatType, DomainType, bool, Vec<Value>)> {
    match t {
        TUInt(m) => {
            match soa {
                SoA::Scalar(xs) => {
                    SoA::Scalar((m, d, false, xs))
                }
                SoA::Empty => SoA::Empty,
                _ => panic!(),
            }
        }
        TBool(m) => {
            match soa {
                SoA::Scalar(xs) => {
                    let m2 = match m.modulus {
                        Some(ref m) => m,
                        _ => panic!("Infinite modulus not supported in $post"),
                    };
                    let need_check_bit = m2 > &Integer::from(2);
                    SoA::Scalar((m, d, need_check_bit, xs))
                }
                SoA::Empty => SoA::Empty,
                _ => panic!(),
            }
        }
        TTuple(ts) => {
            match soa {
                SoA::Tuple(tuple) => {
                    SoA::Tuple(ts.iter().zip(tuple.into_iter()).map(|(t, soa)| {
                        match t {
                            TQualify(t, _s, d) => soa_add_moduli_and_domains_and_need_check_bit(t, *d, soa),
                            _ => panic!(),
                        }
                    }).collect())
                }
                SoA::Empty => SoA::Empty,
                s => panic!("{:?}", s),
            }
        }
        _ => panic!(),
    }
}

// generated from ZKSC code
fn add_pre_const_u793_hof(ctx: &ContextRef, stack: &mut Stack, ts: &Vec<TypeEnum>, vs: &Vec<Value>) -> Value {
    add_pre_const_u793(ctx, &mut stack.scope(), get_tenat(&ts[0]), &vs[0], &vs[1])
}

// generated from ZKSC code
#[allow(non_snake_case,unused_variables)]
fn add_pre_const_u793(ctx: &ContextRef, stack: &mut Stack, N_u843: &NatType, c_u841: &Value, x_u842: &Value) -> Value {
    let t_u6526 = ();
    let t_u6525 = &{
        wire(ctx, &TQualify(&TUInt(N_u843), Pre, Public), &ctx.scalar, c_u841)
    };
    let t_u6524 = &cast_to_domain(ctx, Prover, t_u6525);
    let t_u6522 = &with_loc(ctx,"+ at Vec.zksc:122:5-32", || {add(ctx, N_u843, Post, Prover, t_u6524, x_u842)});
    t_u6522.clone()
}

// generated from ZKSC code
#[allow(non_snake_case,unused_variables)]
fn add_preuint_uv_u794(ctx: &ContextRef, stack: &mut Stack, N_u846: &NatType, c_u844: &Value, xs_u845: &Value) -> Value {
    let f_u955 = &with_loc(ctx,"add_pre_const at Vec.zksc:126:13-29", || {call_hof_initial(ctx, add_pre_const_u793_hof, "add_pre_const_u793", 1, 2, vec![TENat(N_u846.clone())], vec![c_u844.clone()], vec![SoA::Scalar((N_u846, true))], true)});
    let t_u6529 = &zip_hof(ctx, stack, SoA::Scalar(N_u846), vec![SoA::Scalar(N_u846)], vec![xs_u845.clone()], f_u955);
    t_u6529.clone()
}

// generated from ZKSC code
#[allow(non_snake_case,unused_variables)]
fn check_bit_uv_u803(ctx: &ContextRef, stack: &mut Stack, N_u870: &NatType, xs_u869: &Value) -> unit {
    let t_u6545 = &int_literal(ctx, N_u870, 0 /* value: 0 */);
    let t_u6546 = &int_literal(ctx, N_u870, 1 /* value: 1 */);
    let t_u6544 = &with_loc(ctx,"- at Vec.zksc:188:43", || {sub(ctx, N_u870, Pre, Public, t_u6545, t_u6546)});
    let t2_u963 = &with_loc(ctx,"add_preuint_uv at Vec.zksc:188:27-49", || {add_preuint_uv_u794(ctx, &mut stack.scope(), N_u870, t_u6544, xs_u869)});
    let t3_u964 = &zip(ctx, stack, mul_moduli(ctx, N_u870, Post, Prover), vec![TENat(N_u870.clone()), TEStage(Post), TEDomain(Prover)], vec![xs_u869.clone(), t2_u963.clone()], Some("mul".to_string()), mul_hof);
    let trash_u965 = &zip(ctx, stack, assert_zero_moduli(ctx, Prover, N_u870), vec![TEDomain(Prover), TENat(N_u870.clone())], vec![t3_u964.clone()], Some("assert_zero".to_string()), assert_zero_hof);
    let t_u6542 = ();
    t_u6542
}

#[allow(unused)]
pub fn array_to_post(ctx: &ContextRef, stack: &mut Stack, t: &Type, d: DomainType, v: &Value) -> Value {
    let v = unslice_helper(v);
    let soa = match v.view() {
        ValueView::ArrayBool(xs) => aos_to_soa(&xs.iter().map(|x| rep::Bool::new(*x)).collect()),
        ValueView::ArrayU32(xs) => aos_to_soa(&xs.iter().map(|x| Value::new::<u32>(*x)).collect()),
        ValueView::ArrayU64(xs) => aos_to_soa(&xs.iter().map(|x| Value::new::<u64>(*x)).collect()),
        ValueView::Array(xs) => aos_to_soa(xs),
        _ => panic!("array_to_post: not a supported array element type"),
    };
    let soa = soa_add_moduli_and_domains_and_need_check_bit(t, d, soa);
    let soa = soa.map_mut(&mut |(m, d, need_check_bit, xs)| {
        match d {
            Public => {}
            Verifier => {
                xs.iter().for_each(|x| {
                    sieve_backend().add_instance(m, x);
                });
            }
            Prover => {
                xs.iter().for_each(|x| {
                    sieve_backend().add_witness(m, x);
                });
            }
        };
        let wr =
            if NEED_REL {
                match d {
                    Public => {
                        let wocs = xs.iter().map(|x| {
                            WireOrConst::C(get_pre_or_post_uint_or_bool(ctx, m, x))
                        }).collect();
                        sieve_backend().create_vector(m, wocs)
                    }
                    Verifier => sieve_backend().get_instance_wr(m, xs.len()),
                    Prover => {
                        let wr = sieve_backend().get_witness_wr(m, xs.len());
                        // For bool[N] @prover (N > 2), check that each value is a bit.
                        if need_check_bit {
                            let xs_unknown = xs.iter().map(|_| ctx.unknown.clone()).collect();
                            let uint_arr = rep::PostSoA::new(SoA::Scalar((wr.clone(), xs_unknown)));
                            let uint_arr = if use_iter_plugin(ctx) {
                                uint_arr
                            } else {
                                thaw_helper(&uint_arr)
                            };
                            check_bit_uv_u803(ctx, stack, m, &uint_arr);
                        }
                        wr
                    }
                }
            } else {
                sieve_backend().zero_wire_range(m, xs.len())
            };
        (wr, xs)
    });
    let res = rep::PostSoA::new(soa);
    if use_iter_plugin(ctx) {
        res
    } else {
        thaw_helper(&res)
    }
}

#[allow(unused)]
pub fn array_to_prover(_ctx: &ContextRef, _m: &NatType, v: &Value) -> Value {
    v.clone()
}

pub fn unslice_helper(v: &Value) -> Value {
    match v.view() {
        ValueView::Slice(v, ir) => {
            match v.view() {
                ValueView::Array(arr) => {
                    rep::Array::new(arr[ir.first .. ir.first + ir.length].to_vec())
                }
                ValueView::ArrayU8(arr) => {
                    rep::ArrayU8::new(arr[ir.first .. ir.first + ir.length].to_vec())
                }
                ValueView::ArrayU16(arr) => {
                    rep::ArrayU16::new(arr[ir.first .. ir.first + ir.length].to_vec())
                }
                ValueView::ArrayU32(arr) => {
                    rep::ArrayU32::new(arr[ir.first .. ir.first + ir.length].to_vec())
                }
                ValueView::ArrayU64(arr) => {
                    rep::ArrayU64::new(arr[ir.first .. ir.first + ir.length].to_vec())
                }
                ValueView::ArrayBool(arr) => {
                    rep::ArrayBool::new(arr[ir.first .. ir.first + ir.length].to_vec())
                }
                ValueView::ArrayUnit(_len) => {
                    rep::ArrayUnit::new(ir.length)
                }
                ValueView::PostSoA(soa) => {
                    rep::PostSoA::new(soa.map_ref(&|(wr, arr)| (wr.slice(ir), arr[ir.first .. ir.first + ir.length].to_vec())))
                }
                _ => panic!("slice must contain a list or array"),
            }
        }
        _ => v.clone(),
    }
}

#[allow(unused)]
pub fn unslice(
    _ctx: &ContextRef,
    _s_elem: StageType,
    _d_elem: DomainType,
    _d_length: DomainType,
    x: &Value,
) -> Value {
    unslice_helper(x)
}

#[allow(unused)]
pub fn call_hof_initial(_ctx: &ContextRef, f: FnHOF, name: &'static str, total_ts: usize, total_vs: usize, ts: Vec<TypeEnum>, vs: Vec<Value>, sieve_env_moduli: Vec<SoA<(&NatType, bool)>>, is_sieve: bool) -> Value {
    if vs.len() <= total_vs {
        rep::FunValue::new(Box::new(HOF {
            f: f,
            name,
            remaining_type_args: total_ts - ts.len(),
            remaining_value_args: total_vs - vs.len(),
            type_args: ts,
            value_args: vs,
            sieve_env_moduli: sieve_env_moduli.into_iter().map(|soa| soa.map(&|(m, is_pre_public)| (m.clone(), is_pre_public))).collect(),
            is_sieve,
        }))
    } else {
        panic!("Global functions cannot be called with more arguments than they expect, even if they return another function. The call should be split into two separate calls, e.g. (f(x))(y).");
    }
}

#[allow(unused)]
pub fn call_hof_next(ctx: &ContextRef, stack: &mut Stack, f: &Value, mut ts: Vec<TypeEnum>, vs: Vec<Value>, output_moduli: SoA<&NatType>, sieve_env_moduli: Vec<SoA<(&NatType, bool)>>) -> Value {
    let f = get_vfun(f);

    let mut new_sieve_env_moduli = Vec::with_capacity(f.sieve_env_moduli.len() + sieve_env_moduli.len());
    if f.is_sieve {
        for soa in &f.sieve_env_moduli {
            new_sieve_env_moduli.push(soa.clone());
        }
        for soa in &sieve_env_moduli {
            new_sieve_env_moduli.push(soa.map_ref(&|(m, is_pre_public)| ((*m).clone(), *is_pre_public)));
        }
    }


    // NOTE: Type arguments have to all be applied at once on the first call. Lambas will be monomorphic.
    zksc_assert_panic!(ctx, f.remaining_type_args >= ts.len(),
        "Passing too many type arguments to a higher-order function.");
    let mut type_args = f.type_args.clone();
    let remaining_type_args = f.remaining_type_args - ts.len();
    type_args.append(&mut ts);

    let mut value_args = f.value_args.clone();
    let mut remaining_value_args = f.remaining_value_args;
    let mut args_to_go = vs.len();
    let vs_len = vs.len();
    let mut vs_iter = vs.into_iter();
    loop {
        if remaining_value_args == 0 {
            if f.is_sieve {
                if args_to_go > 0 {
                    panic!("SIEVE IR functions cannot return functions");
                }
                let new_sieve_env_moduli_ref: Vec<_> = new_sieve_env_moduli.iter().map(|soa| soa.elems_to_ref().map_ref(&|(m, is_pre_public)| (m, *is_pre_public))).collect();
                let val = call_sieve(ctx, &mut stack.scope(), (output_moduli, new_sieve_env_moduli_ref), type_args, value_args, f.name.to_string(), f.f);
                return val;
            } else {
                let val = (f.f)(ctx, &mut stack.scope(), &type_args, &value_args);
                if args_to_go > 0 {
                    let new_sieve_env_moduli = sieve_env_moduli[value_args.len() ..].to_vec();
                    return call_hof_next(ctx, &mut stack.scope(), &val, vec![], vs_iter.collect(), output_moduli, new_sieve_env_moduli);
                } else {
                    return val;
                }
            }
        }

        if let Some(arg) = vs_iter.next() {
            value_args.push(arg);
            remaining_value_args -= 1;
            args_to_go -= 1;
        }
        else {
            break;
        }
    }

    rep::FunValue::new(Box::new(HOF {
             f: f.f,
             name: f.name,
             remaining_type_args,
             remaining_value_args,
             type_args,
             value_args,
             sieve_env_moduli: new_sieve_env_moduli,
             is_sieve: f.is_sieve,
         }))
}

#[allow(unused)]
pub fn challenge(ctx: &ContextRef, m: &NatType, n: &Value) -> Value {
    let n = get_pre_uint_inf(n).to_usize().expect("Challenge count does not fit `usize`");
    match CURR_DOMAIN {
        Public => ctx.unknown.clone(),
        _ => sieve_challenge(ctx, m, n),
    }
}
