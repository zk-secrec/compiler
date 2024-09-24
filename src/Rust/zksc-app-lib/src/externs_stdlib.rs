/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

 use crate::externs_header::*;
use crate::value::*;
use crate::value_conversions::*;
use crate::builtins::{is_unknown_or_part_of_unknown,get_vstore_mut};

// Add an element to the end of a list, increasing the length of the list by 1.
#[allow(unused)]
pub fn list_push(_: &ContextRef, _: &mut Stack, _q: QualifiedType, _dl: DomainType, xs: &mut Value, x: &Value) {
    if !is_unknown_or_part_of_unknown(xs) {
        xs.make_shallow_copy_if_not_unique();
        match xs.view_mut() {
            ValueViewMut::Array(xs) => xs.push(x.clone()),
            ValueViewMut::ArrayU8(xs) => xs.push(value_to_u8(x)),
            ValueViewMut::ArrayU16(xs) => xs.push(value_to_u16(x)),
            ValueViewMut::ArrayU32(xs) => xs.push(value_to_u32(x)),
            ValueViewMut::ArrayU64(xs) => xs.push(value_to_u64(x)),
            ValueViewMut::ArrayU128(xs) => xs.push(value_to_u128(x)),
            ValueViewMut::ArrayBool(xs) => xs.push(value_to_bool(x)),
            _ => panic!("list_push: not a list"),
        }
    }
}

#[allow(unused)]
pub fn set_store_default(_: &ContextRef, _: &mut Stack, _m: &NatType, _d: DomainType, st: &mut Value, def: bool) {
    if !is_unknown_or_part_of_unknown(st) {
        st.make_shallow_copy_if_not_unique();
        let st = get_vstore_mut(st);
        st.def = def;
    }
}
