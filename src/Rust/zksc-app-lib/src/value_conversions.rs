/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use crate::value::*;
use crate::consts::*;
use crate::context::*;
use crate::zksc_types::*;

use num_bigint::BigInt;

impl<'a> From<&'a mut Value> for &'a mut BigInt {
    fn from(x: &'a mut Value) -> &'a mut BigInt {
        if x.get_count() > 1 {
            x.assign(&Value::new::<BigInt>(x.unwrap::<BigInt>().clone()));
        }
        x.unwrap_mut::<BigInt>()
    }
}

impl<'a> From<&'a Value> for &'a BigInt {
    fn from(x: &'a Value) -> &'a BigInt {
        x.unwrap::<BigInt>()
    }
}

impl From<BigInt> for Value {
    fn from(x: BigInt) -> Value {
        Value::new::<BigInt>(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut String {
    fn from(x: &'a mut Value) -> &'a mut String {
        if x.get_count() > 1 {
            let x2: &String = (&*x).into();
            x.assign(&rep::Str::new(x2.clone()));
        }
        match x.view_mut() {
            ValueViewMut::Str(s) => s,
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a String {
    fn from(x: &'a Value) -> &'a String {
        match x.view() {
            ValueView::Str(s) => s,
            _ => panic!(),
        }
    }
}

impl From<String> for Value {
    fn from(x: String) -> Value {
        rep::Str::new(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Box<[Value]> {
    fn from(x: &'a mut Value) -> &'a mut Box<[Value]> {
        x.make_shallow_copy_if_not_unique();
        &mut x.unwrap_mut::<rep::StructValue>().0.fields
    }
}

impl<'a> From<&'a Value> for &'a Box<[Value]> {
    fn from(x: &'a Value) -> &'a Box<[Value]> {
        &x.unwrap::<rep::StructValue>().0.fields
    }
}

impl From<Box<[Value]>> for Value {
    fn from(x: Box<[Value]>) -> Value {
        StructInner::new_tuple(x)
    }
}

impl<'a, T1 : From<&'a Value>, T2: From<&'a Value>> From<&'a Value> for (T1, T2) {
    fn from(x: &'a Value) -> (T1, T2) {
        let fields = &x.unwrap::<rep::StructValue>().0.fields;
        ((&fields[0]).into(), (&fields[1]).into())
    }
}

impl<T1: Into<Value>, T2: Into<Value>> From<(T1, T2)> for Value {
    fn from(x: (T1, T2)) -> Value {
        StructInner::new_tuple(Box::new([x.0.into(), x.1.into()]))
    }
}

impl<'a, T1 : From<&'a Value>, T2: From<&'a Value>, T3: From<&'a Value>> From<&'a Value> for (T1, T2, T3) {
    fn from(x: &'a Value) -> (T1, T2, T3) {
        let fields = &x.unwrap::<rep::StructValue>().0.fields;
        ((&fields[0]).into(), (&fields[1]).into(), (&fields[2]).into())
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>> From<(T1, T2, T3)> for Value {
    fn from(x: (T1, T2, T3)) -> Value {
        StructInner::new_tuple(Box::new([x.0.into(), x.1.into(), x.2.into()]))
    }
}

impl<'a, T1 : From<&'a Value>, T2: From<&'a Value>, T3: From<&'a Value>, T4: From<&'a Value>> From<&'a Value> for (T1, T2, T3, T4) {
    fn from(x: &'a Value) -> (T1, T2, T3, T4) {
        let fields = &x.unwrap::<rep::StructValue>().0.fields;
        ((&fields[0]).into(), (&fields[1]).into(), (&fields[2]).into(), (&fields[3]).into())
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>> From<(T1, T2, T3, T4)> for Value {
    fn from(x: (T1, T2, T3, T4)) -> Value {
        StructInner::new_tuple(Box::new([x.0.into(), x.1.into(), x.2.into(), x.3.into()]))
    }
}

impl<'a, T1 : From<&'a Value>, T2: From<&'a Value>, T3: From<&'a Value>, T4: From<&'a Value>, T5: From<&'a Value>> From<&'a Value> for (T1, T2, T3, T4, T5) {
    fn from(x: &'a Value) -> (T1, T2, T3, T4, T5) {
        let fields = &x.unwrap::<rep::StructValue>().0.fields;
        ((&fields[0]).into(), (&fields[1]).into(), (&fields[2]).into(), (&fields[3]).into(), (&fields[4]).into())
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>, T5: Into<Value>> From<(T1, T2, T3, T4, T5)> for Value {
    fn from(x: (T1, T2, T3, T4, T5)) -> Value {
        StructInner::new_tuple(Box::new([x.0.into(), x.1.into(), x.2.into(), x.3.into(), x.4.into()]))
    }
}

impl<'a> From<&'a mut Value> for &'a mut u8 {
    fn from(x: &'a mut Value) -> &'a mut u8 {
        if x.get_count() > 1 {
            x.assign(&Value::new::<u8>((&*x).into()));
        }
        match x.view_mut() {
            ValueViewMut::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => x.unwrap_mut::<u8>(),
        }
    }
}

impl From<&Value> for u8 {
    fn from(x: &Value) -> u8 {
        match x.view() {
            ValueView::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => *x.unwrap::<u8>(),
        }
    }
}

impl From<u8> for Value {
    fn from(x: u8) -> Value {
        Value::new::<u8>(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut u16 {
    fn from(x: &'a mut Value) -> &'a mut u16 {
        if x.get_count() > 1 {
            x.assign(&Value::new::<u16>((&*x).into()));
        }
        match x.view_mut() {
            ValueViewMut::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => x.unwrap_mut::<u16>(),
        }
    }
}

impl From<&Value> for u16 {
    fn from(x: &Value) -> u16 {
        match x.view() {
            ValueView::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => *x.unwrap::<u16>(),
        }
    }
}

impl From<u16> for Value {
    fn from(x: u16) -> Value {
        Value::new::<u16>(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut u32 {
    fn from(x: &'a mut Value) -> &'a mut u32 {
        if x.get_count() > 1 {
            x.assign(&Value::new::<u32>((&*x).into()));
        }
        match x.view_mut() {
            ValueViewMut::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => x.unwrap_mut::<u32>(),
        }
    }
}

impl From<&Value> for u32 {
    fn from(x: &Value) -> u32 {
        match x.view() {
            ValueView::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => *x.unwrap::<u32>(),
        }
    }
}

impl From<u32> for Value {
    fn from(x: u32) -> Value {
        Value::new::<u32>(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut u64 {
    fn from(x: &'a mut Value) -> &'a mut u64 {
        if x.get_count() > 1 {
            x.assign(&Value::new::<u64>((&*x).into()));
        }
        match x.view_mut() {
            ValueViewMut::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => x.unwrap_mut::<u64>(),
        }
    }
}

impl From<&Value> for u64 {
    fn from(x: &Value) -> u64 {
        match x.view() {
            ValueView::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => *x.unwrap::<u64>(),
        }
    }
}

impl From<u64> for Value {
    fn from(x: u64) -> Value {
        Value::new::<u64>(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut u128 {
    fn from(x: &'a mut Value) -> &'a mut u128 {
        if x.get_count() > 1 {
            x.assign(&Value::new::<u128>((&*x).into()));
        }
        match x.view_mut() {
            ValueViewMut::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => x.unwrap_mut::<u128>(),
        }
    }
}

impl From<&Value> for u128 {
    fn from(x: &Value) -> u128 {
        match x.view() {
            ValueView::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => *x.unwrap::<u128>(),
        }
    }
}

impl From<u128> for Value {
    fn from(x: u128) -> Value {
        Value::new::<u128>(x)
    }
}

impl<'a> From<&'a mut Value> for &'a mut bool {
    fn from(x: &'a mut Value) -> &'a mut bool {
        if x.get_count() > 1 {
            x.assign(&rep::Bool::new((&*x).into()));
        }
        match x.view_mut() {
            ValueViewMut::Bool(x) => x,
            ValueViewMut::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => panic!(),
        }
    }
}

impl From<&Value> for bool {
    fn from(x: &Value) -> bool {
        match x.view() {
            ValueView::Bool(x) => *x,
            ValueView::Unknown(_) => panic!("Primitive values of higher domain than the current context are not supported in FFI."),
            _ => panic!(),
        }
    }
}

impl From<bool> for Value {
    fn from(x: bool) -> Value {
        rep::Bool::new(x)
    }
}

impl From<&Value> for () {
    fn from(_: &Value) -> () {
    }
}

impl From<()> for Value {
    fn from(_: ()) -> Value {
        rep::Unit::new()
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<u8> {
    fn from(x: &mut Value) -> &mut Vec<u8> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU8(xs) => xs,
            ValueViewMut::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<u8> {
    fn from(x: &Value) -> &Vec<u8> {
        match x.view() {
            ValueView::ArrayU8(xs) => xs,
            ValueView::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl From<Vec<u8>> for Value {
    fn from(xs: Vec<u8>) -> Value {
        rep::ArrayU8::new(xs)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<u16> {
    fn from(x: &mut Value) -> &mut Vec<u16> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU16(xs) => xs,
            ValueViewMut::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<u16> {
    fn from(x: &Value) -> &Vec<u16> {
        match x.view() {
            ValueView::ArrayU16(xs) => xs,
            ValueView::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl From<Vec<u16>> for Value {
    fn from(xs: Vec<u16>) -> Value {
        rep::ArrayU16::new(xs)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<u32> {
    fn from(x: &mut Value) -> &mut Vec<u32> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU32(xs) => xs,
            ValueViewMut::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<u32> {
    fn from(x: &Value) -> &Vec<u32> {
        match x.view() {
            ValueView::ArrayU32(xs) => xs,
            ValueView::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl From<Vec<u32>> for Value {
    fn from(xs: Vec<u32>) -> Value {
        rep::ArrayU32::new(xs)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<u64> {
    fn from(x: &mut Value) -> &mut Vec<u64> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU64(xs) => xs,
            ValueViewMut::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<u64> {
    fn from(x: &Value) -> &Vec<u64> {
        match x.view() {
            ValueView::ArrayU64(xs) => xs,
            ValueView::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl From<Vec<u64>> for Value {
    fn from(xs: Vec<u64>) -> Value {
        rep::ArrayU64::new(xs)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<u128> {
    fn from(x: &mut Value) -> &mut Vec<u128> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayU128(xs) => xs,
            ValueViewMut::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<u128> {
    fn from(x: &Value) -> &Vec<u128> {
        match x.view() {
            ValueView::ArrayU128(xs) => xs,
            ValueView::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl From<Vec<u128>> for Value {
    fn from(xs: Vec<u128>) -> Value {
        rep::ArrayU128::new(xs)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<bool> {
    fn from(x: &mut Value) -> &mut Vec<bool> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::ArrayBool(xs) => xs,
            ValueViewMut::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<bool> {
    fn from(x: &Value) -> &Vec<bool> {
        match x.view() {
            ValueView::ArrayBool(xs) => xs,
            ValueView::Array(_) => panic!("Boxed arrays of primitive types (generated in polymorphic functions) not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            _ => panic!(),
        }
    }
}

impl From<Vec<bool>> for Value {
    fn from(xs: Vec<bool>) -> Value {
        rep::ArrayBool::new(xs)
    }
}

impl<'a> From<&'a mut Value> for &'a mut Vec<Value> {
    fn from(x: &mut Value) -> &mut Vec<Value> {
        x.make_shallow_copy_if_not_unique();
        match x.view_mut() {
            ValueViewMut::Array(xs) => xs,
            ValueViewMut::ArrayU8(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueViewMut::ArrayU16(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueViewMut::ArrayU32(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueViewMut::ArrayU64(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueViewMut::ArrayU128(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueViewMut::ArrayBool(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueViewMut::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            ValueViewMut::PostSoA(..) => panic!("Vectors with $post elements not supported in FFI."),
            _ => panic!(),
        }
    }
}

impl<'a> From<&'a Value> for &'a Vec<Value> {
    fn from(x: &Value) -> &Vec<Value> {
        match x.view() {
            ValueView::Array(xs) => xs,
            ValueView::ArrayU8(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueView::ArrayU16(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueView::ArrayU32(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueView::ArrayU64(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueView::ArrayU128(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueView::ArrayBool(_) => panic!("Unboxed arrays in polymorphic functions expecting boxed arrays not supported in FFI."),
            ValueView::Slice(..) => panic!("Slices not supported in FFI. Use the builtin unslice to convert a slice into a normal list or vector."),
            ValueView::PostSoA(..) => panic!("Vectors with $post elements not supported in FFI."),
            _ => panic!(),
        }
    }
}

impl From<Vec<Value>> for Value {
    fn from(xs: Vec<Value>) -> Value {
        rep::Array::new(xs)
    }
}

#[inline(always)]
pub fn u8_to_value(ctx: &ContextRef, d: DomainType, x: u8) -> Value {
    if d <= CURR_DOMAIN {
        Value::new::<u8>(x)
    } else {
        ctx.unknown.clone()
    }
}

#[inline(always)]
pub fn u16_to_value(ctx: &ContextRef, d: DomainType, x: u16) -> Value {
    if d <= CURR_DOMAIN {
        Value::new::<u16>(x)
    } else {
        ctx.unknown.clone()
    }
}

#[inline(always)]
pub fn u32_to_value(ctx: &ContextRef, d: DomainType, x: u32) -> Value {
    if d <= CURR_DOMAIN {
        Value::new::<u32>(x)
    } else {
        ctx.unknown.clone()
    }
}

#[inline(always)]
pub fn u64_to_value(ctx: &ContextRef, d: DomainType, x: u64) -> Value {
    if d <= CURR_DOMAIN {
        Value::new::<u64>(x)
    } else {
        ctx.unknown.clone()
    }
}

#[inline(always)]
pub fn u128_to_value(ctx: &ContextRef, d: DomainType, x: u128) -> Value {
    if d <= CURR_DOMAIN {
        Value::new::<u128>(x)
    } else {
        ctx.unknown.clone()
    }
}

#[inline(always)]
pub fn bool_to_value(ctx: &ContextRef, d: DomainType, x: bool) -> Value {
    if d <= CURR_DOMAIN {
        rep::Bool::new(x)
    } else {
        ctx.unknown.clone()
    }
}

#[inline(always)]
pub fn unit_to_value(ctx: &ContextRef, _d: DomainType, _x: ()) -> Value {
    ctx.scalar.clone()
}

#[inline(always)]
pub fn value_to_u8(x: &Value) -> u8 {
    match x.view() {
        ValueView::Unknown(_) => 0,
        _ => *x.unwrap::<u8>(),
    }
}

#[inline(always)]
pub fn value_to_u16(x: &Value) -> u16 {
    match x.view() {
        ValueView::Unknown(_) => 0,
        _ => *x.unwrap::<u16>(),
    }
}

#[inline(always)]
pub fn value_to_u32(x: &Value) -> u32 {
    match x.view() {
        ValueView::Unknown(_) => 0,
        _ => *x.unwrap::<u32>(),
    }
}

// Get value of uint[2^64] $pre @D
#[inline(always)]
pub fn value_to_u64(x: &Value) -> u64 {
    match x.view() {
        ValueView::Unknown(_) => 0,
        _ => *x.unwrap::<u64>(),
    }
}

#[inline(always)]
pub fn value_to_u128(x: &Value) -> u128 {
    match x.view() {
        ValueView::Unknown(_) => 0,
        _ => *x.unwrap::<u128>(),
    }
}

// Get value of bool[N] $pre @D
#[inline(always)]
pub fn value_to_bool(x: &Value) -> bool {
    match x.view() {
        ValueView::Bool(x) => *x,
        ValueView::Unknown(_) => false,
        _ => panic!("value_to_bool: {:?}", x),
    }
}

#[inline(always)]
pub fn value_to_unit(_x: &Value) {
}

