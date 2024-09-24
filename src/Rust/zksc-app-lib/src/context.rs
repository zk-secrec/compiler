/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use std::{
    cell::RefCell,
    collections::{HashMap,HashSet},
    fmt,
    rc::Rc,
};

use log::info;
use num_traits::{One, Zero};
use thiserror::Error;

use crate::builtins::TypeEnum;
use crate::integer::*;
use crate::stack::Stack;
use crate::stack::StackMemory;
use crate::value::*;
use crate::zksc_types::*;
use crate::circuit_parser::*;
use crate::sieve::*;
use num_bigint::BigInt;

pub type ResourceLoader<T> = Box<dyn FnMut(String) -> Option<Rc<T>>>;

pub struct Context {
    pub input_public: HashMap<String, Value>,
    pub input_instance: HashMap<String, Value>,
    pub input_witness: HashMap<String, Value>,
    pub sieve_functions: RefCell<HashMap<(String, Vec<TypeEnum>, Vec<Integer>, Vec<Vec<usize>>), usize>>, // maps the name of a ZKSC function, its type parameters, its $pre @public parameters, and its list lengths to the UID of a SIEVE function
    pub circuit_loader: RefCell<ResourceLoader<Circuit>>,
    pub is_inside_sieve_fn_def: RefCell<bool>,
    pub is_inside_sieve_fn_call: RefCell<bool>,
    pub sieve_fn_witness_count: RefCell<u64>, // number of witness values inside the current sieve fn definition, used for the disjunction plugin
    pub integer_zero: Integer,
    pub integer_one: Integer,
    pub stack_trace: RefCell<Vec<&'static str>>,
    pub message_stack: RefCell<Vec<&'static str>>,
    pub scalar: Value,
    pub unknown: Value,
    pub part_of_unknown: Value,
    pub string_literals: Vec<Value>,
    pub nat_type_literals: Vec<NatType>,
    pub assert_error: RefCell<Option<AssertError>>,
    pub integer_literal_count: usize,
    pub integer_literal_cache: Vec<Value>,
    pub supported_fields: HashSet<BigInt>,
    pub supported_challenges: HashSet<BigInt>,
    pub supported_conversions: HashSet<(BigInt, BigInt)>,
    pub supported_plugins: HashSet<String>,
    pub is_iter_available: bool,
    // TODO: I feel like it should be possible to replace it with a single stack.
    pub free_rewind_stacks: RefCell<Vec<StackMemory>>,
}

#[derive(Error, Debug, Clone)]
#[error("assertion error")]
pub struct AssertError {
    pub reason: Vec<&'static str>,
}

#[derive(Error, Debug)]
pub enum ZkscUserError {
    #[error(transparent)]
    AssertError(#[from] AssertError),
    #[error("deserialization error")]
    JsonError(#[from] serde_json::Error),
    #[error("unsupported json value `{0}`")]
    JsonUnsupportValue(serde_json::Value),
}

pub type Result<T> = core::result::Result<T, ZkscUserError>;


pub type ContextRef = Rc<Context>;

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Context")
    }
}

fn parse_json_from_slice<S: AsRef<str>>(slice: S) -> Result<HashMap<String, Value>> {
    use serde_json::Value as sv;
    let v = serde_json::from_str(slice.as_ref())?;

    fn parse_sv(sv: &sv) -> Result<Value> {
        let result = match sv {
            sv::Bool(b) => rep::Bool::new(*b),
            sv::String(s) => Value::new::<BigInt>(string_to_integer(s)),
            sv::Array(xs) => {
                let vs : Result<_> = xs.into_iter().map(parse_sv).collect();
                rep::Array::new(vs?)
            }
            _ => Err(ZkscUserError::JsonUnsupportValue(sv.clone()))?,
        };
        Ok(result)
    }

    let m = match v {
        sv::Object(m) => m,
        _ => Err(ZkscUserError::JsonUnsupportValue(v))?,
    };
    let m: Result<HashMap<_, _>> = m.into_iter().map(|(k, v)| parse_sv(&v).map(|v| { (k, v)})).collect();
    Ok(m?)
}

fn make_circuit_loader(mut str_loader: ResourceLoader<str>) -> ResourceLoader<Circuit> {
    type CircuitMap = HashMap<String, Rc<Circuit>>;
    use std::collections::hash_map::Entry::*;
    let mut circuit_map: CircuitMap = HashMap::new();
    let load_circuit = move |circuit_name: String| -> Option<Rc<Circuit>> {
        match circuit_map.entry(circuit_name.clone()) {
            Occupied(occ) => Some(occ.get().clone()),
            Vacant(vac) => match (*str_loader)(circuit_name.clone()) {
                Some(text) => {
                    info!("Loading circuit '{circuit_name}'");
                    let circuit = Rc::new(parse_circuit_from_str(text.as_ref()));
                    vac.insert(circuit.clone());
                    Some(circuit)
                }
                None => None,
            },
        }
    };

    Box::new(load_circuit)
}

impl Context {
    pub fn new(
        input_public: Option<&str>,
        input_instance: Option<&str>,
        input_witness: Option<&str>,
        circuit_content_loader: ResourceLoader<str>,
        integer_literals: Vec<BigInt>,
        string_literals: Vec<Value>,
        nat_type_literals: Vec<NatType>,
        supported_fields: Vec<BigInt>,
        supported_challenges: Vec<BigInt>,
        supported_conversions: Vec<(BigInt, BigInt)>,
        is_iter_available: bool,
        supported_plugins: Vec<&str>,
    ) -> Result<Context> {
        let circuit_loader = RefCell::new(make_circuit_loader(circuit_content_loader));
        let is_inside_sieve_fn_def = RefCell::new(false);
        let is_inside_sieve_fn_call = RefCell::new(false);
        let sieve_fn_witness_count = RefCell::new(0);
        let input_public = input_public.map_or(Ok(HashMap::new()), parse_json_from_slice)?;
        let input_instance = input_instance
            .map_or(Ok(HashMap::new()), parse_json_from_slice)?;
        let input_witness = input_witness.map_or(Ok(HashMap::new()), parse_json_from_slice)?;
        let sieve_functions = RefCell::new(HashMap::new());
        let integer_zero = Integer::zero();
        let integer_one = Integer::one();
        let scalar = rep::Unit::new();
        let part_of_unknown = rep::PartOfUnknown::new();
        let unknown = rep::Unknown::new(part_of_unknown.clone());
        let stack_trace = RefCell::new(Vec::new());
        let trace_trace = RefCell::new(Vec::new());
        let mut integer_literal_cache = Vec::new();
        for (i, n) in nat_type_literals.iter().enumerate() {
            assert!(n.tag == i as u64, "");
        }
        let integer_literal_count = integer_literals.len();
        integer_literal_cache.reserve(nat_type_literals.len() * integer_literal_count);
        for m in nat_type_literals.iter() {
            for lit in integer_literals.iter() {
                integer_literal_cache.push((m.from_bigint)(&lit))
            }
        }
        let assert_error = RefCell::new(None);

        let supported_fields = HashSet::from_iter(supported_fields.into_iter());
        let supported_challenges = HashSet::from_iter(supported_challenges.into_iter());
        let supported_conversions = HashSet::from_iter(supported_conversions.into_iter());
        let supported_plugins = HashSet::from_iter(supported_plugins.into_iter().map(|s| String::from(s)));

        let free_rewind_stacks = RefCell::new(Vec::new());

        Ok(Context {
            input_public,
            input_instance,
            input_witness,
            sieve_functions,
            circuit_loader,
            is_inside_sieve_fn_def,
            is_inside_sieve_fn_call,
            sieve_fn_witness_count,
            stack_trace,
            message_stack: trace_trace,
            integer_zero,
            integer_one,
            scalar,
            unknown,
            part_of_unknown,
            string_literals,
            nat_type_literals,
            assert_error,
            integer_literal_count,
            integer_literal_cache,
            supported_fields,
            supported_challenges,
            supported_conversions,
            supported_plugins,
            is_iter_available,
            free_rewind_stacks,
        })
    }

    pub fn finalize(&self) -> Result<()> {
        sieve_backend().finalize();
        // NOTE: This clears any outstanding assert_error (replaces it with None)
        if let Some(err) = self.assert_error.take() {
            Err(err)?;
        }
        Ok(())
    }

    pub fn nat_inf(&self) -> &NatType {
        assert!(! self.nat_type_literals.is_empty());
        let ret = &self.nat_type_literals[0];
        assert!(ret.modulus.is_none());
        ret
    }

    pub fn nat_2(&self) -> &NatType {
        assert!(self.nat_type_literals.len() >= 1);
        &self.nat_type_literals[1]
    }

    pub fn with_rewind_stack<F>(&self, func: F)
        where F : FnOnce(&mut Stack)
    {
        let mem = self.make_rewind_stack();
        mem.unwrap_with_lock(|mut stack| { func(&mut stack); });
        self.restore_rewind_stack(mem);
    }

    fn make_rewind_stack(&self) -> StackMemory {
        match self.free_rewind_stacks.borrow_mut().pop() {
            Some(mem) => mem,
            None => StackMemory::new(1024*1024),
        }
    }

    fn restore_rewind_stack(&self, mem: StackMemory) {
        self.free_rewind_stacks.borrow_mut().push(mem);
    }

    pub fn inside_sieve_fn_def(&self) -> bool {
        *self.is_inside_sieve_fn_def.borrow()
    }

    pub fn inside_sieve_fn_call(&self) -> bool {
        *self.is_inside_sieve_fn_call.borrow()
    }
}
