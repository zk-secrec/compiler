/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use crate::ContextRef;
use crate::for_each_zksc_type;
use crate::stack::Stack;
use crate::sieve::*;
use crate::builtins::*;
use crate::generated::*;
use crate::zksc_integer::BitwiseBigInt;
use num_bigint::BigInt;
use std::{
    rc::Rc,
    ptr::NonNull,
};

/// Reference counted value.
///
/// The pointed-to memory region contains tag, reference count, and data.
pub struct Value {
    ptr: NonNull<u8>,
}

// TODO: Display values of ZkscDefined types as well.
impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.view() {
            ValueView::Unknown(v) => f.debug_tuple("Value::Unknown").field(v).finish(),
            ValueView::Unit() => f.debug_tuple("Value::Unit").finish(),
            ValueView::Bool(b) => f.debug_tuple("Value::Bool").field(b).finish(),
            ValueView::Str(s) => f.debug_tuple("Value::Str").field(s).finish(),
            ValueView::Post(w, v) => f.debug_tuple("Value::Post").field(w).field(v).finish(),
            ValueView::Array(v) => f.debug_tuple("Value::Array").field(v).finish(),
            ValueView::ArrayU8(v) => f.debug_tuple("Value::ArrayU8").field(v).finish(),
            ValueView::ArrayU16(v) => f.debug_tuple("Value::ArrayU16").field(v).finish(),
            ValueView::ArrayU32(v) => f.debug_tuple("Value::ArrayU32").field(v).finish(),
            ValueView::ArrayU64(v) => f.debug_tuple("Value::ArrayU64").field(v).finish(),
            ValueView::ArrayU128(v) => f.debug_tuple("Value::ArrayU128").field(v).finish(),
            ValueView::ArrayBool(v) => f.debug_tuple("Value::ArrayBool").field(v).finish(),
            ValueView::ArrayUnit(v) => f.debug_tuple("Value::ArrayUnit").field(v).finish(),
            ValueView::PartOfUnknown() => f.debug_tuple("Value::PartOfUnknown").finish(),
            ValueView::StoreValue(st) => f.debug_tuple("Value::StoreValue").field(st).finish(),
            ValueView::FunValue(v) => f.debug_tuple("Value::FunValue").field(v).finish(),
            ValueView::ZkscDefined() => f.debug_tuple("Value::ZkscDefined").finish(),
            ValueView::StructValue(inner) => {
                let mut builder = f.debug_tuple("Value::StructValue");
                for v in inner.fields.iter() {
                    builder.field(v);
                }

                builder.finish()
            }
            ValueView::PostSoA(soa) => f.debug_tuple("Value::SoA").field(soa).finish(),
            ValueView::Slice(v, ir) => f.debug_tuple("Value::Slice").field(v).field(ir).finish(),
            ValueView::Tensor(v, dim) => f.debug_tuple("Value::Tensor").field(v).field(dim).finish(),
        }
    }
}

// In this macro we list all supported values with their tag and internal representation.
// We use this information to define all functions to manipulate
macro_rules! for_each_builtin_type {
    ($continuation:ident) => {
        $continuation! {
            (Unknown,            0, (Value)), // the argument is PartOfUnknown, so that we can get from &'a mut Unknown to &'a mut PartOfUnknown without changing the lifetime
            (Unit,               1, ()),
            (Bool,               2, (bool)),
            (Str,                3, (String)),
            (Post,               4, (Wire, Value)),
            (Array,              5, (Vec<Value>)),
            (ArrayU8,            6, (Vec<u8>)), // unboxed array of u8 values
            (ArrayU16,           7, (Vec<u16>)), // unboxed array of u16 values
            (ArrayU32,           8, (Vec<u32>)), // unboxed array of u32 values
            (ArrayU64,           9, (Vec<u64>)), // unboxed array of u64 values
            (ArrayU128,         10, (Vec<u128>)), // unboxed array of u128 values
            (ArrayBool,         11, (Vec<bool>)), // unboxed array of bool values
            (ArrayUnit,         12, (usize)), // unboxed array of unit values, represented as the length
            (PartOfUnknown,     13, ()), // part of a value with unknown structure or size; unlike Unknown, it remains unknown even if a known value is assigned to it
            (StoreValue,        14, (Box<Store>)),
            (FunValue,          15, (Box<HOF>)),
            (StructValue,       16, (StructInner)),
            (PostSoA,           17, (SoA<(WireRange, Vec<Value>)>)),
            (Slice,             18, (Value, IndexRange)), // the Value is Array or PostSoA
            (Tensor,            19, (Value, Vec<usize>)) // the Value is Array or PostSoA or Slice
        }
    };
}

// TODO: This has un-necessary layer of indirection. Unfortunately no ?Sized types supported yet.
// TODO: Storing full finalizer is also un-necessary because as we could roll struct indentity
// strictly into the tag and then dispatch dtor based on the tag as with all other values.
// This requires signficant rework including removing context from the finalizer.
#[derive(Clone)]
pub struct StructInner {
    pub fields: Box<[Value]>,
    pub finalizer: FinalizerRef,
}

pub type FinalizerRef = Option<Rc<Finalizer>>;

// TODO: We store reference to context, but this is conceptually not necessary as we have a single context per thread.
// However, fixing that requires more significant work.
pub struct Finalizer {
    ctx: ContextRef,
    callback: Box<dyn Fn(&ContextRef, &mut Stack, &Value)>,
}

impl Finalizer {
    pub fn new(ctx: &ContextRef, callback: Box<dyn Fn(&ContextRef, &mut Stack, &Value)>) -> Finalizer {
        Finalizer { ctx: Rc::clone(ctx), callback }
    }
}

impl StructInner {
    pub fn new(fields: Box<[Value]>, finalizer: FinalizerRef) -> Value {
        rep::StructValue::new(StructInner { fields, finalizer })
    }

    pub fn new_tuple(fields: Box<[Value]>) -> Value {
        StructInner::new(fields, None)
    }
}

impl std::fmt::Debug for StructInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StructInner").field("fields",&self.fields).finish()
    }
}

impl Drop for StructInner {
    fn drop(&mut self) {
        let StructInner { fields, finalizer } = &mut *self;
        match finalizer {
            None => {},
            Some(ptr) => {
                let Finalizer { ctx, callback } = ptr.as_ref();
                // Need to take care to not call the dtor twice!
                let mut new_fields : Box<[Value]> = Box::default();
                std::mem::swap(fields, &mut new_fields);
                let value = StructInner::new(new_fields, None);
                ctx.with_rewind_stack(|stack| {
                    callback(&ctx, stack, &value);
                });
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct ZkscPrimVtable {
    dealloc: fn(&Value, *mut u8),
}

impl std::fmt::Debug for ZkscPrimVtable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ZkscPrimVtable").finish()
    }
}

impl ZkscPrimVtable {
    const fn null() -> Self {
        Self { dealloc: |_, _| { } }
    }
}

impl ZkscPrimVtable {
    const fn new(dealloc: fn(&Value, *mut u8)) -> ZkscPrimVtable {
        ZkscPrimVtable { dealloc }
    }
}

macro_rules! map_token_to_one {
    ($_:tt) => { 1 }
}

macro_rules! make_value_ctor {
    ($name:ident, ()) => {
        #[inline]
        pub fn new() -> Value {
            Value::new::<$name>($name())
        }
    };

    ($name:ident, ($t:ty,)) => {
        #[inline]
        pub fn new(p0: $t) -> Value {
            Value::new::<$name>($name(p0))
        }
    };

    ($name:ident, ($t1:ty, $t2:ty,)) => {
        #[inline]
        pub fn new(p0: $t1, p1: $t2) -> Value {
            Value::new::<$name>($name(p0, p1))
        }
    };
}

macro_rules! construct_value_view {
    ($name:ident, $args:ident, ()) => {
        ValueView::$name()
    };
    ($name:ident, $args:ident, ($t:ty,)) => {
        ValueView::$name(&$args.0)
    };
    ($name:ident, $args:ident, ($t1:ty, $t2:ty,)) => {
        ValueView::$name(&$args.0, &$args.1)
    };
}

macro_rules! construct_value_view_mut {
    ($name:ident, $args:ident, ()) => {
        ValueViewMut::$name()
    };
    ($name:ident, $args:ident, ($t:ty,)) => {
        ValueViewMut::$name(&mut $args.0)
    };
    ($name:ident, $args:ident, ($t1:ty, $t2:ty,)) => {
        ValueViewMut::$name(&mut $args.0, &mut $args.1)
    };
}

macro_rules! register_zksc_types {
    ($(($name:ident, $i:literal)),*$(,)?) => {
        pub const NUMBER_OF_ZKSC_TYPES : usize = $(map_token_to_one!{$name}+)* 0;

        pub const ZKSC_TYPE_TABLE : [ZkscPrimVtable; NUMBER_OF_ZKSC_TYPES] = [
            $($name :: TYPE_INFO, )*
        ];

        $(
            impl RepresentableValue for $name {
                const TAG: u64 = $i + NUMBER_OF_BUILTIN_TYPES as u64;
                const TYPE_INFO: ZkscPrimVtable = {
                    let fun_ptr = |_ : &Value, ptr| unsafe { Value :: dealloc_inner_ptr :: < $name > (ptr)  };
                    ZkscPrimVtable::new(fun_ptr)
                };
            }
        )*
    }
}

macro_rules! register_builtin_types {
    ($(($name:ident, $i:literal, ($($rep:ty),*))),*) => {
        const NUMBER_OF_BUILTIN_TYPES : usize = $(map_token_to_one!{$name}+)* 0;

        const BUILTIN_TYPE_TABLE : [ZkscPrimVtable; NUMBER_OF_BUILTIN_TYPES] = [
            $(rep :: $name :: TYPE_INFO, )*
        ];

        // Internal representation types
        pub mod rep {
            use super::*;

            $(
                #[derive(Debug)]
                pub struct $name ($(pub $rep,)*);
                impl $name {
                    fn dealloc(_value: &Value, ptr: * mut u8) {
                        unsafe {
                            Value::dealloc_inner_ptr::<Self>(ptr);
                        }
                    }
                }
                impl RepresentableValue for $name {
                    const TAG: u64 = $i;
                    const TYPE_INFO: ZkscPrimVtable =
                        ZkscPrimVtable::new($name :: dealloc);
                }
                impl $name {
                    make_value_ctor!{$name, ($($rep,)*)}
                }
            )*
        }

        pub enum ValueView<'a> {
            $($name ($(&'a $rep,)*),)*
            ZkscDefined()
        }

        pub enum ValueViewMut<'a> {
            $($name ($(&'a mut $rep,)*),)*
            ZkscDefinedMut()
        }

        // Generate Value::view() for inspecting primitive types.
        impl Value {
            #[inline]
            pub fn view(&self) -> ValueView<'_> {
                let tag = self.get_tag() as usize;
                match tag {
                    $(
                        $i => {
                            let _args = &self.as_ref::<rep :: $name>().1;
                            construct_value_view!{$name, _args, ($($rep,)*)}
                        }
                    ,)*
                    _ => ValueView :: ZkscDefined()
                }
            }

            #[inline]
            pub fn view_mut(&self) -> ValueViewMut<'_> {
                let tag = self.get_tag() as usize;
                match tag {
                    $(
                        $i => {
                            let _args = &mut self.as_mut_ref::<rep :: $name>().1;
                            construct_value_view_mut!{$name, _args, ($($rep,)*)}
                        }
                    ,)*
                    _ => ValueViewMut :: ZkscDefinedMut()
                }
            }
        }
    }
}

for_each_builtin_type! {register_builtin_types}
for_each_zksc_type! {register_zksc_types}

const NUMBER_OF_TYPES: usize = NUMBER_OF_BUILTIN_TYPES + NUMBER_OF_ZKSC_TYPES;

const TYPE_TABLE : [ZkscPrimVtable; NUMBER_OF_TYPES] = {
    let mut out = [ZkscPrimVtable::null(); NUMBER_OF_TYPES];
    let mut i = 0;
    while i < NUMBER_OF_BUILTIN_TYPES {
        out[i] = BUILTIN_TYPE_TABLE[i];
        i = i + 1;
    }
    while i < NUMBER_OF_TYPES {
        out[i] = ZKSC_TYPE_TABLE[i - NUMBER_OF_BUILTIN_TYPES];
        i = i + 1;
    }
    out
};

/// Trait for all representable values.
pub trait RepresentableValue {
    const TAG: u64;
    const TYPE_INFO: ZkscPrimVtable;
}

const TAG_BITS: u64 = 16;
const TAG_MASK: u64 = (1 << TAG_BITS) - 1;

impl Value {
    #[inline]
    fn as_mut_ptr<T: RepresentableValue>(&self) -> *mut (u64, T) {
        self.ptr.as_ptr().cast()
    }

    #[inline]
    fn as_mut_ref<T: RepresentableValue>(&self) -> &mut (u64, T) {
        unsafe { &mut *self.as_mut_ptr::<T>() }
    }

    #[inline]
    fn as_ref<T: RepresentableValue>(&self) -> &(u64, T) {
        self.as_mut_ref()
    }

    #[inline]
    fn get_count_and_tag(&self) -> u64 {
        self.as_ref::<()>().0
    }

    #[inline]
    pub fn get_count(&self) -> u64 {
        self.get_count_and_tag() >> TAG_BITS
    }

    #[inline]
    fn get_tag(&self) -> u64 {
        self.as_ref::<()>().0 & TAG_MASK
    }

    #[inline]
    unsafe fn increment(&self) {
        let count: &mut u64 = &mut self.as_mut_ref::<()>().0;
        *count = (*count).wrapping_add(1 << TAG_BITS);
    }

    #[inline]
    unsafe fn decrement(&self) {
        let count: &mut u64 = &mut self.as_mut_ref::<()>().0;
        *count = (*count).wrapping_sub(1 << TAG_BITS);
    }

    #[inline]
    pub fn get<T: RepresentableValue>(&self) -> Option<&T> {
        if T::TAG == self.get_tag() {
            Some(&self.as_ref::<T>().1)
        }
        else {
            None
        }
    }

    #[inline]
    pub fn unwrap<T: RepresentableValue>(&self) -> &T {
        self.get().unwrap()
    }

    #[inline]
    fn get_mut<T: RepresentableValue>(&self) -> Option<&mut T> {
        if T::TAG == self.get_tag() {
            Some(&mut self.as_mut_ref::<T>().1)
        }
        else {
            None
        }
    }

    #[inline]
    pub fn unwrap_mut<T: RepresentableValue>(&self) -> &mut T {
        self.get_mut().unwrap()
    }

    #[inline]
    pub fn assign(&mut self, v: &Value) {
        // drop the inner pointer
        unsafe {
            self.decrement();
            if self.get_count() == 0 {
                (TYPE_TABLE.get_unchecked(self.get_tag() as usize).dealloc)(self, self.ptr.as_ptr());
            }
        }
        // point it to the new value
        self.ptr = v.ptr;
        unsafe {
            self.increment();
        }
    }

    // If the same value of ptr is used in another Value, then
    // make a shallow copy of the data behind ptr and point self.ptr to this new copy.
    // After that, the elements of the data can be changed without changing other copies.
    // The pointers below the top level can still be shared with outer Values.
    // Thus if elements deeper than the top level need to be changed, then this function
    // has to be called several times, once for each pointer leading to the changed value
    // (but not the changed value itself, as it will be overwritten).
    // Thus if x.y.z needs to be changed, then do
    //   x.make_shallow_copy_if_not_unique();
    //   x.y.make_shallow_copy_if_not_unique();
    //   x.y.z.assign(...);
    #[inline]
    pub fn make_shallow_copy_if_not_unique(&mut self) {
        //println!("make_shallow_copy_if_not_unique: refcount = {}", self.get_count());
        if self.get_count() > 1 {
            match self.get_tag() {
                rep::Array::TAG => self.make_shallow_copy_helper::<rep::Array>(|rep0| rep::Array(rep0.0.clone())),
                rep::ArrayU8::TAG => self.make_shallow_copy_helper::<rep::ArrayU8>(|rep0| rep::ArrayU8(rep0.0.clone())),
                rep::ArrayU16::TAG => self.make_shallow_copy_helper::<rep::ArrayU16>(|rep0| rep::ArrayU16(rep0.0.clone())),
                rep::ArrayU32::TAG => self.make_shallow_copy_helper::<rep::ArrayU32>(|rep0| rep::ArrayU32(rep0.0.clone())),
                rep::ArrayU64::TAG => self.make_shallow_copy_helper::<rep::ArrayU64>(|rep0| rep::ArrayU64(rep0.0.clone())),
                rep::ArrayU128::TAG => self.make_shallow_copy_helper::<rep::ArrayU128>(|rep0| rep::ArrayU128(rep0.0.clone())),
                rep::ArrayBool::TAG => self.make_shallow_copy_helper::<rep::ArrayBool>(|rep0| rep::ArrayBool(rep0.0.clone())),
                rep::StructValue::TAG => self.make_shallow_copy_helper::<rep::StructValue>(|rep0| rep::StructValue(rep0.0.clone())),
                rep::StoreValue::TAG => self.make_shallow_copy_helper::<rep::StoreValue>(|rep0| rep::StoreValue(rep0.0.clone())),
                t => panic!("make_shallow_copy_if_not_unique not implemented for tag {} (it should only be called for structured values)", t),
            }
        }
        assert!(self.get_count() == 1);
    }

    // Immutable version which returns the copy instead of modifying self. Reference count is not checked in this version.
    #[inline]
    pub fn make_shallow_copy(&self) -> Value {
        match self.get_tag() {
            rep::Array::TAG => self.make_shallow_copy_new::<rep::Array>(|rep0| rep::Array(rep0.0.clone())),
            rep::ArrayU8::TAG => self.make_shallow_copy_new::<rep::ArrayU8>(|rep0| rep::ArrayU8(rep0.0.clone())),
            rep::ArrayU16::TAG => self.make_shallow_copy_new::<rep::ArrayU16>(|rep0| rep::ArrayU16(rep0.0.clone())),
            rep::ArrayU32::TAG => self.make_shallow_copy_new::<rep::ArrayU32>(|rep0| rep::ArrayU32(rep0.0.clone())),
            rep::ArrayU64::TAG => self.make_shallow_copy_new::<rep::ArrayU64>(|rep0| rep::ArrayU64(rep0.0.clone())),
            rep::ArrayU128::TAG => self.make_shallow_copy_new::<rep::ArrayU128>(|rep0| rep::ArrayU128(rep0.0.clone())),
            rep::ArrayBool::TAG => self.make_shallow_copy_new::<rep::ArrayBool>(|rep0| rep::ArrayBool(rep0.0.clone())),
            rep::StructValue::TAG => self.make_shallow_copy_new::<rep::StructValue>(|rep0| rep::StructValue(rep0.0.clone())),
            rep::StoreValue::TAG => self.make_shallow_copy_new::<rep::StoreValue>(|rep0| rep::StoreValue(rep0.0.clone())),
            t => panic!("make_shallow_copy not implemented for tag {} (it should only be called for structured values)", t),
        }
    }

    #[inline]
    fn make_shallow_copy_helper<T: RepresentableValue>(&mut self, clone_fn: fn(&T) -> T) {
        let rep0: &T = self.unwrap::<T>();
        let rep: T = clone_fn(rep0);
        let tag_and_count: u64 = (1u64 << TAG_BITS) | self.get_tag();
        unsafe {
            let ptr = NonNull::new_unchecked(Box::leak(Box::<(u64, T)>::new((tag_and_count, rep))));
            // decrease reference count of the old copy; it cannot get 0 here as it was > 1
            self.decrement();
            // point to the new copy, which has reference count 1
            self.ptr = ptr.cast();
        }
    }

    #[inline]
    fn make_shallow_copy_new<T: RepresentableValue>(&self, clone_fn: fn(&T) -> T) -> Value {
        Value::new(clone_fn(self.unwrap::<T>()))
    }

    #[inline]
    pub fn new<T: RepresentableValue>(rep: T) -> Self {
        unsafe {
            let tag_and_count: u64 = (1u64 << TAG_BITS) | (T::TAG as u64);
            let ptr = NonNull::new_unchecked(Box::leak(Box::<(u64, T)>::new((tag_and_count, rep))));
            Value { ptr: ptr.cast() }
        }
    }

    #[inline]
    pub unsafe fn dealloc_inner_ptr<T>(ptr: * mut u8) {
        drop(Box::<(u64, T)>::from_raw(ptr.cast()));
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        unsafe {
            //println!("Value::drop: tag = {}, refcount = {}", self.get_tag(), self.get_count());
            self.decrement();
            if self.get_count() == 0 {
                (TYPE_TABLE.get_unchecked(self.get_tag() as usize).dealloc)(self, self.ptr.as_ptr());
            }
        }
    }
}

impl Clone for Value {
    fn clone(&self) -> Value {
        unsafe {
            //println!("Value::clone: tag = {}, refcount = {}", self.get_tag(), self.get_count());
            self.increment();
            Value { ptr: self.ptr }
        }
    }
}

fn drop_unit(_value: &Value, ptr: * mut u8) {
    unsafe {
        Value::dealloc_inner_ptr::<()>(ptr);
    }
}

impl RepresentableValue for () {
    const TAG: u64 = 0;
    const TYPE_INFO: ZkscPrimVtable = ZkscPrimVtable::new(drop_unit);
}
