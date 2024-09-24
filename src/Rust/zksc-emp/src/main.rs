/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use num_traits::ToPrimitive;
use simple_logger::SimpleLogger;
use zksc_app_lib::command_line::*;
use zksc_app_lib::*;

//include bindings for emp backend
mod libemp {
    #![allow(dead_code)]
    #![allow(non_snake_case)]
    #![allow(non_camel_case_types)]
    #![allow(non_upper_case_globals)]
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

use libemp::*;

use std::any::Any;

use std::borrow::{Borrow, BorrowMut};
use std::collections::VecDeque;
use std::ffi::CString;
use std::mem::size_of;
use std::os::raw::c_void as Void;
use std::{
    cell::RefCell,
    io::{self, BufWriter},
    rc::Rc,
};

#[derive(Clone, Debug)]
struct EmpWire {
    opaque_value: usize,
}

impl WireTrait for EmpWire {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

fn downcast_wire(w: &Wire) -> &EmpWire {
    w.downcast::<EmpWire>()
}

pub(crate) struct EMP {
    env: RefCell<*mut Void>,
    instance_queue : RefCell<VecDeque<u64>>,
    witness_queue : RefCell<VecDeque<u64>>
}

macro_rules! voidm {
    ($e:expr) => {
        $e as *mut Void
    };
}

fn drop_emp_wire(s: usize) {
    drop(unsafe { Box::from_raw(s as *mut u128) });
}

const QUEUE_CAPACITY : usize = 200;

impl EMP {
    pub fn new() -> EMP {
        let mut addr_parts = EMP_ADDRESS.split(":");

        let domain_nr = get_domain_nr(&CURR_DOMAIN);
        let ip_cstr = CString::new(addr_parts.next().expect("No network address for emp")).unwrap();
        let ip_string_pointer = ip_cstr.into_raw();
        /*
        CString::into_raw doc states that:
        The pointer which this function returns must be returned to Rust and reconstituted using CString::from_raw to be properly deallocated.
        Specifically, one should not use the standard C free() function to deallocate this string.
        Failure to call CString::from_raw will lead to a memory leak.

        This is why I move the raw pointer value to pointer_numbercopy and then read it back to trash
        */

        let pointer_numbercopy = ip_string_pointer as usize;
        let env_ptr = unsafe {
            init_env(
                ip_string_pointer,
                addr_parts
                    .next()
                    .expect("No network port for emp")
                    .parse::<i32>()
                    .expect("Can't parse emp network port"),
                domain_nr,
                1,
            )
        };
        let env = RefCell::new(env_ptr);

        let _ = unsafe { CString::from_raw(pointer_numbercopy as *mut i8) };
        let witness_queue = RefCell::new(VecDeque::with_capacity(QUEUE_CAPACITY));
        let instance_queue  = RefCell::new(VecDeque::with_capacity(QUEUE_CAPACITY));
        EMP { env, witness_queue, instance_queue }
    }

    fn perform_binary_op<F>(&self, f: F, w1: &Wire, w2: &Wire) -> Wire
    where
        F: Fn(*mut Void, *mut Void, *mut Void),
    {
        let res_addr: *mut u128 = Box::leak(Box::new(0));

        let input_1_addr: *mut u128 = downcast_wire(w1).opaque_value as *mut u128;
        let input_2_addr: *mut u128 = downcast_wire(w2).opaque_value as *mut u128;

        f(voidm!(input_1_addr), voidm!(input_2_addr), voidm!(res_addr));

        upcast_wire(EmpWire { opaque_value : res_addr as usize })
    }

    fn emp_clone_wire(&self, w: &Wire) -> Wire {
        self.perform_unary_op(|a, b| unsafe { r_copy_val(a, b) }, w)
    }

    fn perform_unary_op<F>(&self, f: F, w1: &Wire) -> Wire
    where
        F: Fn(*mut Void, *mut Void),
    {
        let res_addr: *mut u128 = &mut *Box::leak(Box::new(0));

        let input_addr = downcast_wire(w1).opaque_value as *mut u128;
        f(voidm!(input_addr), voidm!(res_addr));

        upcast_wire(EmpWire { opaque_value : res_addr as usize })
    }

    fn new_wire(&self, value: u64, domain_nr: i32) -> Wire {
        let res_addr: *mut u128 = &mut *Box::leak(Box::new(0));

        unsafe { r_int_new(voidm!(res_addr), value, domain_nr) };

        upcast_wire(EmpWire { opaque_value : res_addr as usize })
    }

    fn unwrap_value_u64(&self, m: &NatType, value : &Value) -> u64 {
        match value.view() {
            ValueView::Unknown(_) => 0,
            ValueView::ZkscDefined() => (m.to_bigint)(value).to_u64().expect("variable too big for backend"),
            ValueView::Bool(b) => if *b { 1 } else { 0 },
            //VBool(_) => panic!("bools aren't supported in backend"),
            _ => panic!("Unknown Value to convert to u64 : {:?}", value),
        }
    }

    fn new_var(&self, m: &NatType, value: &Value, domain_nr: i32) -> Wire {
        match value.view() {
            ValueView::Unknown(_) => self.new_wire(0, domain_nr),
            ValueView::ZkscDefined() => {
                let val_u64 = (m.to_bigint)(value).to_u64().expect("variable too big for backend");
                self.new_wire(val_u64, domain_nr)
            }
            ValueView::Bool(b) => self.new_wire(if *b { 1 } else { 0 }, domain_nr),
            //VBool(_) => panic!("bools aren't supported in backend"),
            _ => panic!("Unknown variable to make: {:?}", value),
        }
    }
}

fn get_domain_nr(d: &DomainType) -> i32 {
    match d {
        Public => 0,
        Prover => 1,
        Verifier => 2,
    }
}

impl SIEVEIR for EMP {
    
    fn and(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        //NatInf is just a placeholder. modulus is fixed M61 anyway
        self.mul(m, w1, w2)
    }

    fn xor(&self, _m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        self.perform_binary_op(|a, b, res| unsafe { r_int_xor(a, b, res) }, w1, w2)
    }

    fn not(&self, _m: &NatType, w1: &Wire) -> Wire {
        self.perform_unary_op(|a, res| unsafe { r_int_not(a, res) }, w1)
    }

    fn const_bool(&self, m: &NatType, w1: bool) -> Wire {
        self.new_var(m, &rep::Bool::new(w1), get_domain_nr(&Public))
    }

    fn copy_bool(&self, _m: &NatType, w1: &Wire) -> Wire {
        self.emp_clone_wire(w1)
    }

    fn mul(&self, _m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        self.perform_binary_op(|a, b, res| unsafe { r_int_mul(a, b, res) }, w1, w2)
    }

    fn add(&self, _m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        self.perform_binary_op(|a, b, res| unsafe { r_int_add(a, b, res) }, w1, w2)
    }

    fn mulc(&self, modulus: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let c = self.new_wire(
            c2.to_u64().expect("mulc: constant doesn't fit in u64"),
            get_domain_nr(&Public),
        );
        self.mul(modulus, w1, &c)
    }

    fn addc(&self, modulus: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let c = self.new_wire(
            c2.to_u64().expect("mulc: constant doesn't fit in u64"),
            get_domain_nr(&Public),
        );
        self.add(modulus, w1, &c)
    }

    fn assert_zero(&self, _m: &NatType, w1: &Wire) {
        let input_1_addr: *mut u128 = downcast_wire(w1).opaque_value as *mut u128;
        unsafe { r_assert_zero(voidm!(input_1_addr)) }
    }

    fn assert_eq(&self, _m1: &NatType, w1: &Wire, _m2: &NatType, w2: &Wire) {
        let input_1_addr: *mut u128 = downcast_wire(w1).opaque_value as *mut u128;
        let input_2_addr: *mut u128 = downcast_wire(w2).opaque_value as *mut u128;
        unsafe { r_assert_eq(voidm!(input_1_addr), voidm!(input_2_addr)) }
    }

    fn assert_eq_scalar_vec(&self, _m1: &NatType, w1: &Wire, _m2: &NatType, wires: Vec<Wire>) {
        let wires: Vec<EmpWire> = wires.iter().map(|w| downcast_wire(w).clone()).collect();
        let a = wires.as_ptr();
        unsafe {
            r_assert_eq_uints_bools(
                voidm!(downcast_wire(w1).opaque_value as *mut u128),
                a as *mut Void,
                wires.len() as u64,
                size_of::<EmpWire>() as i32,
            )
        }
    }

    fn get_instance(&self, m: &NatType) -> Wire {
        match self.instance_queue.borrow_mut().pop_front() {
            Some(v) => {
                self.new_wire(v, get_domain_nr(&Verifier))
            },
            None => {
                panic!("get_instance called but instance queue empty")
            }
        }
    }

    fn get_witness(&self, _m: &NatType) -> Wire {
        match self.witness_queue.borrow_mut().pop_front() {
            Some(v) => {
                self.new_wire(v, get_domain_nr(&Prover))
            },
            None => {
                panic!("get_witness called but witness queue empty")
            }
        }
    }

    fn add_instance(&self, _m: &NatType, _x: &Value) {
        let as_u64 = self.unwrap_value_u64(_m,_x);
        self.instance_queue.borrow_mut().push_back(as_u64);
    }

    fn add_witness(&self, _m: &NatType, _x: &Value) {
        let as_u64 = self.unwrap_value_u64(_m,_x);
        self.witness_queue.borrow_mut().push_back(as_u64);
    }

    fn flush(&self) {
        () // this function is for text generation
    }

    fn bool2int(&self, _m: &NatType, w1: &Wire, _output_modulus: &NatType) -> Wire {
        self.perform_unary_op(|a, b| unsafe { r_copy_val(a, b) }, w1)
    }

    fn int_field_switch(&self, _m: &NatType, w: &Wire, output_modulus: &NatType) -> Wire {
        match output_modulus.modulus {
            Some(ref m) => {
                if m.to_u64()
                    .expect("field switching: modulus too big for emp backend")
                    == 2305843009213693951
                {
                    self.emp_clone_wire(w)
                } else {
                    panic!("field switching: unsuitable modulus for backend: {:?}", m)
                }
            },
            _ => self.emp_clone_wire(w),
        }
    }

    fn clone_wire(&self, w1: &Wire) -> Wire {
        self.emp_clone_wire(w1)
    }

    fn finalize(&self) {
        let env_ptr = *self.env.borrow();
        unsafe { del_env(env_ptr) }
    }

    fn zero_wire(&self, _m: &NatType) -> Wire {
        upcast_wire(EmpWire { opaque_value: std::ptr::null::<()>() as usize })
    }

    fn drop_wire(&self, wire: &mut Wire) {
        drop_emp_wire(downcast_wire(wire).opaque_value);
    }
}

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
    let sieve: Box<dyn SIEVEIR> = Box::new(EMP::new());
    set_boxed_sieve_backend(sieve);
    zksc_run(
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
    )
}
