/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use crate::integer::*;
use crate::stack::*;
use crate::value::*;
use core::fmt::Debug;
use std::fmt;
use num_bigint::BigInt;
use std::hash::{Hash, Hasher};

/*
#[derive(Clone, Debug, PartialEq)]
pub enum NatType {
    Nat(Integer),
    NatInf,
}
*/

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum StageType {
    Pre,
    Post,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd)]
pub enum DomainType {
    Public,
    Verifier,
    Prover,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[allow(unused)]
pub enum Type<'a> {
    TUnit,
    TBool(&'a NatType),
    TUInt(&'a NatType),
    TList(&'a Type<'a>),
    TTuple(&'a [&'a Type<'a>]),
    TStore(&'a Type<'a>, &'a Type<'a>),
    TQualify(&'a Type<'a>, StageType, DomainType),
}

pub use DomainType::*;
//pub use NatType::*;
pub use StageType::*;
pub use Type::*;

impl<'a> Type<'a> {
    pub fn contains_scalar_with_stage(&self, self_stage: StageType, s: StageType) -> bool {
        match self {
            TQualify(t, s2, _d) => t.contains_scalar_with_stage(*s2, s),
            TTuple(ts) => {
                for t in *ts {
                    if t.contains_scalar_with_stage(self_stage, s) {
                        return true;
                    }
                }
                return false;
            }
            TList(t) => t.contains_scalar_with_stage(self_stage, s),
            TStore(_, _) => panic!("contains_scalar_with_stage cannot be used with stores"),
            _ => self_stage == s,
        }
    }
}

pub fn tcast_stage(s: StageType, d: DomainType) -> StageType {
    match (s,d) {
        (Pre,_) => Pre,
        (s,Public) => s,
        (_,Verifier) => Pre,
        (_,Prover) => Pre,
    }
}

pub fn tcast_domain(d1: DomainType, d2: DomainType) -> DomainType {
    match (d1,d2) {
        (Public,d) => d,
        (d,Public) => d,
        (Prover,_) => Prover,
        (_,Prover) => Prover,
        (Verifier,Verifier) => Verifier,
    }
}

#[allow(suspicious_double_ref_op)]
pub fn tcast_unqual<'b, 'a : 'b>(stack: &'b Stack, t: &'a Type<'a>, d: DomainType) -> &'b Type<'b> {
    match t {
        TUnit => &TUnit,
        TBool(n) => stack.alloc(TBool(n.clone())),
        TUInt(n) => stack.alloc(TUInt(n.clone())),
        TList(t) => stack.alloc(TList(tcast_unqual(stack, t, d))),
        TTuple(ts) => {
            let ts = stack.alloc_slice_fill_iter(ts.iter().map(|t| { tcast_unqual(stack, t, d) }));
            stack.alloc(TTuple(ts))
        },
        TStore(t1, t2) => stack.alloc(TStore(tcast_unqual(stack,t1,d), tcast_unqual(stack,t2,d))),
        TQualify(u,s,d0) => stack.alloc(TQualify(tcast_unqual(stack,u,d), tcast_stage(*s,d), tcast_domain(*d0,d))),
    }
}

#[derive(Clone)]
pub struct NatType {
    pub tag: u64,
    pub modulus: Option<BigInt>,
    pub modulus_value: fn() -> Value,
    pub is_zero : fn(&Value) -> bool,
    pub is_one : fn(&Value) -> bool,
    pub eq : fn(&Value, &Value) -> bool,
    pub lt : fn(&Value, &Value) -> bool,
    pub add : fn(&Value, &Value) -> Value,
    pub mul : fn(&Value, &Value) -> Value,
    pub sub : fn(&Value, &Value) -> Value,
    pub div: fn(&Value, &Value) -> Value,
    pub hmod: fn(&Value,&Value) -> Value,
    pub mod_div : fn(&Value,&Value) -> Value,
    pub to_bigint: fn(&Value) -> Integer,
    pub from_bigint: fn(&Integer) -> Value,
    pub fmt: fn(&Value, &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl PartialEq for NatType {
    fn eq(&self, other: &Self) -> bool {
        self.tag == other.tag
    }
}

impl Eq for NatType { }

impl Debug for NatType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NatType")
            .field("tag", &self.tag)
            .field("modulus", &self.modulus)
            .finish()
    }
}

impl Hash for NatType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
    }
}
