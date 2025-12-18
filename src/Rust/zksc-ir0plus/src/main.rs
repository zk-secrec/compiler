/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use num_traits::One;
use simple_logger::SimpleLogger;
use zksc_app_lib::oob_challenge::OobChallengeBackend;
use zksc_app_lib::zksc_integer::ZkscIntDisplay;
use std::fmt;
use std::any::Any;
use std::fs::File;
use std::io::BufWriter;
use std::io::Stdout;
use std::io::Write;
use std::rc::Rc;
use std::{cell::RefCell, io};

use zksc_app_lib::command_line::*;
use zksc_app_lib::*;

const IR_VERSION: &str = "2.1.0";

const EMIT_NEW_WIRE: bool = false; // if true then emit @new for single wires
const EMIT_NEW_WIRE_RANGE: bool = false; // if true then emit @new for wire ranges
const EMIT_DELETE_WIRE: bool = false; // if true then emit @delete for single wires
const EMIT_DELETE_WIRE_RANGE: bool = false; // if true then emit @delete for wire ranges

// This wrapper is needed in order to print moduli without incurring extra allocations.
struct ModulusFieldName<'a>(&'a NatType);

impl<'a> fmt::Display for ModulusFieldName<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0.modulus {
            Some(_) => write!(f, "{}", self.0.tag - 1),
            None => write!(f, "ZInf"),
        }
    }
}

#[derive(Debug)]
struct IRAllocation {
    field_no: u64,
    first_wire: usize,
    length: usize,
}

#[derive(Debug)]
struct AllocationImpl {
    field_no: u64,
    first_wire: usize,
    length: usize,
}

impl AllocationTrait for AllocationImpl {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl IRAllocation {
    fn new(m: &NatType, first_wire: usize, length: usize) -> Rc<IRAllocation> {
        let field_no = match m.modulus {
            Some(_) => m.tag - 1,
            None => panic!("Infinite modulus not allowed for wires"),
        };
        let alloc = IRAllocation { field_no, first_wire, length };
        let emit_new = if length == 1 {
            EMIT_NEW_WIRE
        } else if length > 1 {
            EMIT_NEW_WIRE_RANGE
        } else {
            false
        };
        if emit_new {
            sieve_backend().declare_new_wire_range(&alloc.to_allocation());
        }
        Rc::new(alloc)
    }

    fn zero() -> Rc<IRAllocation> {
        Rc::new(IRAllocation { field_no: 0, first_wire: 0, length: 0 })
    }

    fn to_allocation_impl(&self) -> AllocationImpl {
        AllocationImpl {
            field_no: self.field_no,
            first_wire: self.first_wire,
            length: self.length,
        }
    }
    fn to_allocation(&self) -> Allocation {
        Allocation::new(self.to_allocation_impl())
    }
}

impl fmt::Display for AllocationImpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.length == 1 {
            write!(f, "{}: ${}", self.field_no, self.first_wire)
        } else {
            write!(f, "{}: ${}...${}", self.field_no, self.first_wire, self.first_wire + self.length - 1)
        }
    }
}

impl Drop for IRAllocation {
    fn drop(&mut self) {
        let emit_delete = if self.length == 1 {
            EMIT_DELETE_WIRE
        } else if self.length > 1 {
            EMIT_DELETE_WIRE_RANGE
        } else {
            false
        };
        if emit_delete {
            sieve_backend().declare_delete_wire_range(&self.to_allocation())
        }
    }
}

#[derive(Clone, Debug)]
struct WireImpl {
    opaque_value: usize,
    alloc: Rc<IRAllocation>,
}

impl WireTrait for WireImpl {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl WireImpl {
    fn new(m: &NatType, wire: usize) -> WireImpl {
        WireImpl { opaque_value: wire, alloc: IRAllocation::new(m, wire, 1) }
    }
}

#[derive(Clone, Debug)]
struct WireRangeImpl {
    first_wire: usize,
    length: usize,
    alloc: Rc<IRAllocation>,
}

impl WireRangeTrait for WireRangeImpl {
    fn length(&self) -> usize {
        self.length
    }

    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl WireRangeImpl {
    fn zero_with_len(len: usize) -> WireRangeImpl {
        WireRangeImpl { first_wire: 0, length: len, alloc: IRAllocation::zero() }
    }

    fn index(&self, i: usize) -> WireImpl {
        assert!(i < self.length);
        WireImpl { opaque_value: self.first_wire + i, alloc: self.alloc.clone() }
    }
}

// This wrapper is needed in order to print wire ranges without incurring extra allocations.
struct WR<'a>(&'a WireRangeImpl);

impl<'a> fmt::Display for WR<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.length == 1 {
            write!(f, "${}", self.0.first_wire)
        } else {
            write!(f, "${}...${}", self.0.first_wire, self.0.first_wire + self.0.length - 1)
        }
    }
}

// Bitwise copy a wire. Not safe in general!
fn bitwise_copy_wire(w: &Wire) -> Wire {
    let w = downcast_wire(w);
    upcast_wire(
        WireImpl {
            opaque_value: w.opaque_value,
            alloc: w.alloc.clone(),
        }
    )
}

// TODO: We have two levels of un-necessary memory allocations with this function.
// First by converting an Iterator to Vec<u64> and second by converting Vec<64> to String.
// We could instead directly pipe wires from itertor to fmt output.
// Second part is low-hanging but first requires little bit of refactoring.
fn wire_list_to_string(wires: Vec<Wire>) -> String {
    let mut s = String::new();
    for w in wires {
        if !s.is_empty() {
            s.push_str(", ");
        }
        s.push('$');
        s.push_str(&(downcast_wire(&w).opaque_value).to_string());
    }
    s
}

pub trait OutputIR0plus {
    fn init_moduli(&self, moduli: &Vec<NatType>);
    fn rel(&self, s: String);
    fn ins(&self, m: &NatType, s: String);
    fn wit(&self, m: &NatType, s: String);
    fn get_rel_size(&self) -> u64;
    fn set_indent(&self, s: &str);
    fn flush_rel(&self);
    fn flush_ins(&self);
    fn flush(&self);
    fn finalize(&self);
}

pub(crate) struct FilesIR0plus {
    prefix: String,
    rel: RefCell<BufWriter<File>>,
    ins: RefCell<Vec<BufWriter<File>>>,
    wit: RefCell<Vec<BufWriter<File>>>,
    indent: RefCell<String>,
    rel_size: RefCell<u64>, // for profiling the rel-file size (number of lines)
}

impl FilesIR0plus {
    pub fn new(prefix: &str) -> FilesIR0plus {
        let rel = RefCell::new(BufWriter::new(File::create(prefix.to_owned() + ".rel").expect("Failed to open file for writing")));
        if NEED_REL {
            writeln!(rel.borrow_mut(), "version {};", IR_VERSION).expect("");
            writeln!(rel.borrow_mut(), "circuit;").expect("");
            if INTERACTIVE {
                rel.borrow_mut().flush().expect("");
            }
        }
        let ins = RefCell::new(Vec::new());
        let wit = RefCell::new(Vec::new());
        let rel_size = RefCell::new(0);
        FilesIR0plus { prefix: prefix.to_owned(), rel, ins, wit, indent: RefCell::new("".to_string()), rel_size }
    }
}


impl OutputIR0plus for FilesIR0plus {
    fn init_moduli(&self, moduli: &Vec<NatType>) {
        for (i,m) in moduli.iter().enumerate() {
            assert!(i == m.tag as usize);
            if i == 0 {
                continue
            }
            let i = i - 1; // the field index in IR0+ is m.tag - 1
            let mut ins = BufWriter::new(File::create(self.prefix.clone() + "_" + &i.to_string() + ".ins").expect("Failed to open file for writing"));
            if CURR_DOMAIN >= Verifier {
                writeln!(ins, "version {};", IR_VERSION).expect("");
                writeln!(ins, "public_input;").expect("");
                writeln!(ins, "@type field {};", m).expect("");
                writeln!(ins, "@begin").expect("");
                if INTERACTIVE {
                    ins.flush().expect("");
                }
            }
            self.ins.borrow_mut().push(ins);
            // challenges do not currently work with IR0+
            //if INTERACTIVE { thread::sleep(time::Duration::from_millis(500)); }
            let mut wit = BufWriter::new(File::create(self.prefix.clone() + "_" + &i.to_string() + ".wit").expect("Failed to open file for writing"));
            if CURR_DOMAIN == Prover {
                writeln!(wit, "version {};", IR_VERSION).expect("");
                writeln!(wit, "private_input;").expect("");
                writeln!(wit, "@type field {};", m).expect("");
                writeln!(wit, "@begin").expect("");
            }
            self.wit.borrow_mut().push(wit);
        }
    }

    fn rel(&self, s: String) {
        writeln!(self.rel.borrow_mut(), "{}{}", self.indent.borrow(), s).expect("");
        let r = *self.rel_size.borrow();
        *self.rel_size.borrow_mut() = r + 1;
    }

    fn ins(&self, m: &NatType, s: String) {
        writeln!(self.ins.borrow_mut()[(m.tag as usize) - 1], "{}", s).expect("");
    }

    fn wit(&self, m: &NatType, s: String) {
        writeln!(self.wit.borrow_mut()[(m.tag as usize) - 1], "{}", s).expect("");
    }

    fn get_rel_size(&self) -> u64 {
        *self.rel_size.borrow()
    }

    fn set_indent(&self, s: &str) {
        *self.indent.borrow_mut() = s.to_string();
    }

    fn flush_rel(&self) {
        self.rel.borrow_mut().flush().expect("");
    }

    fn flush_ins(&self) {
        for f in self.ins.borrow_mut().iter_mut() {
            f.flush().expect("");
        }
    }

    fn flush(&self) {
        self.flush_rel();
        self.flush_ins();
        for f in self.wit.borrow_mut().iter_mut() {
            f.flush().expect("");
        }
    }

    fn finalize(&self) {
        if NEED_REL {
            writeln!(self.rel.borrow_mut(), "@end").expect("");
        }
        if CURR_DOMAIN >= Verifier {
            for f in self.ins.borrow_mut().iter_mut() {
                writeln!(f, "@end").expect("");
            }
        }
        if CURR_DOMAIN == Prover {
            for f in self.wit.borrow_mut().iter_mut() {
                writeln!(f, "@end").expect("");
            }
        }

        self.flush();
    }
}

pub(crate) struct StdoutIR0plus {
    output: Rc<RefCell<BufWriter<Stdout>>>,
    indent: RefCell<String>,
}

impl StdoutIR0plus {
    pub fn new(output: Rc<RefCell<BufWriter<Stdout>>>) -> StdoutIR0plus {
        StdoutIR0plus { output, indent: RefCell::new("".to_string()) }
    }
}

impl OutputIR0plus for StdoutIR0plus {
    fn init_moduli(&self, _moduli: &Vec<NatType>) {}

    fn rel(&self, s: String) {
        writeln!(self.output.borrow_mut(), ".rel: {}{}", self.indent.borrow(), s).expect("");
    }

    fn ins(&self, m: &NatType, s: String) {
        writeln!(self.output.borrow_mut(), "{}.ins: {}", ModulusFieldName(m), s).expect("");
    }

    fn wit(&self, m: &NatType, s: String) {
        writeln!(self.output.borrow_mut(), "{}.wit: {}", ModulusFieldName(m), s).expect("");
    }

    fn get_rel_size(&self) -> u64 {
        0 // return arbitrary value to avoid failing
    }

    fn set_indent(&self, s: &str) {
        *self.indent.borrow_mut() = s.to_string();
    }

    fn flush_ins(&self) {
        self.flush();
    }

    fn flush_rel(&self) {
        self.flush();
    }

    fn flush(&self) {
        self.output.borrow_mut().flush().expect("");
    }

    fn finalize(&self) {
        self.flush();
    }
}
pub struct IR0plus {
    out: Box<dyn OutputIR0plus>,
    next_wire: RefCell<u64>,
    saved_next_wire: RefCell<u64>, // global wire number is saved here while we are in a function
    in_function: RefCell<bool>,
    sieve_fn_names: RefCell<Vec<String>>, // names of SIEVE IR functions corresponding to each UID
    fn_outputs: RefCell<(Vec<String>, Vec<WireImpl>)>, // output moduli (as field number strings) and wires of the function currently being defined
}

impl IR0plus {
    pub fn new(out: Box<dyn OutputIR0plus>) -> IR0plus {
        let next_wire = RefCell::new(0);
        let saved_next_wire = RefCell::new(0);
        let in_function = RefCell::new(false);
        let sieve_fn_names = RefCell::new(Vec::new());
        let fn_outputs = RefCell::new((Vec::new(), Vec::new()));
        IR0plus {
            out,
            next_wire,
            saved_next_wire,
            in_function,
            sieve_fn_names,
            fn_outputs,
        }
    }

    fn new_wire(&self, m: &NatType) -> WireImpl {
        let w = *self.next_wire.borrow();
        *self.next_wire.borrow_mut() = w + 1;
        WireImpl::new(m, w as usize)
    }

    fn wr_new(m: &NatType, first_wire: usize, length: usize) -> WireRangeImpl {
        WireRangeImpl { first_wire, length, alloc: IRAllocation::new(m, first_wire, length) }
    }

    fn new_wire_range(&self, m: &NatType, n: usize) -> WireRangeImpl {
        let w = *self.next_wire.borrow();
        *self.next_wire.borrow_mut() = w + n as u64;
        Self::wr_new(m, w as usize, n)
    }

    fn _declare_new_wire_range(&self, alloc: &AllocationImpl) {
        if alloc.length >= 1 {
            self.out.rel(format!("  @new({});", alloc));
        }
    }

    fn new_function_uid(&self, sieve_fn_name: String) -> usize {
        let uid = self.sieve_fn_names.borrow().len();
        self.sieve_fn_names.borrow_mut().push(sieve_fn_name.clone());
        uid
    }

    fn function_name(&self, uid: usize) -> String {
        self.sieve_fn_names.borrow()[uid].clone()
    }

    fn assign_woc(&self, m: &String, w: &WireImpl, woc: &WireOrConst) {
        match woc {
            WireOrConst::W(w1) => {
                self.out
                    .rel(format!("  ${} <- {}: ${};", w.opaque_value, m, downcast_wire(w1).opaque_value));
            }
            WireOrConst::C(c1) => {
                self.out
                    .rel(format!("  ${} <- {}: <{}>;", w.opaque_value, m, c1));
            }
        }
    }
}

fn moduli_to_string(moduli: &Vec<&NatType>, n: usize) -> String {
    let mut s = String::new();
    for i in 0 .. moduli.len() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!("{}:{}", ModulusFieldName(moduli[i]), n));
    }
    s
}

fn moduli_and_counts_to_string(moduli: &Vec<&NatType>, ns: &Vec<usize>) -> String {
    let mut s = String::new();
    for i in 0 .. moduli.len() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!("{}:{}", ModulusFieldName(moduli[i]), ns[i]));
    }
    s
}

fn downcast_wire(w: &Wire) -> &WireImpl {
    w.downcast::<WireImpl>()
}

fn downcast_wires<'a>(wires: Vec<&'a Wire>) -> Vec<&'a WireImpl> {
    wires.into_iter().map(|w| downcast_wire(w)).collect()
}

fn downcast_wr(wr: &WireRange) -> &WireRangeImpl {
    wr.downcast::<WireRangeImpl>()
}

fn downcast_wrs<'a>(wrs: Vec<&'a WireRange>) -> Vec<&'a WireRangeImpl> {
    wrs.into_iter().map(|wr| downcast_wr(wr)).collect()
}

impl SIEVEIR for IR0plus {
    fn write_headers(&self, ns: &Vec<NatType>, supported_conversions: Vec<(&NatType, &NatType)>, supported_plugins: Vec<&str>) {
        supported_plugins.into_iter().for_each(|s| {
            self.out.rel(format!("@plugin {};", s));
        });
        ns.iter().enumerate().for_each(|(i,n)| {
            match &n.modulus {
                Some(m) => {
                    self.out.rel(format!("@type field {};", m));
                    assert!(i > 0);
                }
                None => assert!(i == 0), // assuming infinite field is first
            }
        });
        supported_conversions.into_iter().for_each(|(m_in,m_out)| {
            self.out.rel(format!("@convert(@out: {}:1, @in: {}:1);", ModulusFieldName(m_out), ModulusFieldName(m_in)));
        });
        self.out.rel("@begin".to_string());
        self.out.init_moduli(ns);
    }

    fn zero_wire(&self, _m: &NatType) -> Wire {
        upcast_wire(WireImpl { opaque_value: 0, alloc: IRAllocation::zero() })
    }

    fn clone_wire(&self, w1: &Wire) -> Wire {
        bitwise_copy_wire(w1)
    }

    fn drop_wire(&self, _wire: &mut Wire) { }

    fn zero_wire_range(&self, _m: &NatType, n: usize) -> WireRange {
        upcast_wr(WireRangeImpl::zero_with_len(n))
    }

    fn clone_wire_range(&self, wr: &WireRange) -> WireRange {
        upcast_wr(downcast_wr(wr).clone())
    }

    fn index_wire_range(&self, wr: &WireRange, i: usize) -> Wire {
        let wr = downcast_wr(wr);
        upcast_wire(wr.index(i))
    }

    fn slice_wire_range(&self, wr: &WireRange, ir: &IndexRange) -> WireRange {
        let wr = downcast_wr(wr);
        assert!(ir.first + ir.length <= wr.length);
        WireRange::new(WireRangeImpl { first_wire: wr.first_wire + ir.first, length: ir.length, alloc: wr.alloc.clone() })
    }

    fn wire_to_wire_range(&self, w: &Wire) -> WireRange {
        let w = downcast_wire(w);
        WireRange::new(
            WireRangeImpl {
                first_wire: w.opaque_value,
                length: 1,
                alloc: w.alloc.clone(),
            }
        )
    }

    // In this backend, IRAllocations are dropped rather than wire ranges, thus nothing needs to be done here.
    fn drop_wire_range(&self, _wire: &mut WireRange) { }

    fn declare_new_wire_range(&self, alloc: &Allocation) {
        let alloc = alloc.downcast::<AllocationImpl>();
        self._declare_new_wire_range(alloc);
    }

    fn declare_delete_wire_range(&self, alloc: &Allocation) {
        let alloc = alloc.downcast::<AllocationImpl>();
        if alloc.length >= 1 {
            self.out.rel(format!("  @delete({});", alloc));
        }
    }

    fn and(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        self.mul(m, w1, w2)
    }

    fn xor(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        self.add(m, w1, w2)
    }

    fn not(&self, m: &NatType, w1: &Wire) -> Wire {
        // IR0+ spec replaces @not(x) with @addc(x, <1>)
        self.addc(m, w1, &Integer::one())
    }

    fn copy_bool(&self, m: &NatType, w1: &Wire) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        self.out
            .rel(format!("  ${} <- {}: ${};", w.opaque_value, ModulusFieldName(m), w1.opaque_value));
        upcast_wire(w)
    }

    fn const_bool(&self, modulus: &NatType, c: bool) -> Wire {
        let w = self.new_wire(modulus);
        self.out.rel(format!(
            "  ${} <- {}: <{}>;",
            w.opaque_value,
            ModulusFieldName(modulus),
            if c { 1 } else { 0 }
        ));
        upcast_wire(w)
    }

    fn const_uint(&self, modulus: &NatType, x: &Value) -> Wire {
        let w = self.new_wire(modulus);
        self.out.rel(format!(
            "  ${} <- {}: <{}>;",
            w.opaque_value,
            ModulusFieldName(modulus),
            ZkscIntDisplay::new(modulus, x)
        ));
        upcast_wire(w)
    }

    fn mul(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        let w2 = downcast_wire(w2);
        self.out.rel(format!(
            "  ${} <- @mul({}: ${}, ${});",
            w.opaque_value,
            ModulusFieldName(m),
            w1.opaque_value,
            w2.opaque_value,
        ));
        upcast_wire(w)
    }

    fn add(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        let w2 = downcast_wire(w2);
        self.out.rel(format!(
            "  ${} <- @add({}: ${}, ${});",
            w.opaque_value,
            ModulusFieldName(m),
            w1.opaque_value,
            w2.opaque_value,
        ));
        upcast_wire(w)
    }

    fn mulc(&self, modulus: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let w = self.new_wire(modulus);
        let w1 = downcast_wire(w1);
        self.out.rel(format!(
            "  ${} <- @mulc({}: ${}, <{}>);",
            w.opaque_value,
            ModulusFieldName(modulus),
            w1.opaque_value,
            c2
        ));
        upcast_wire(w)
    }

    fn addc(&self, modulus: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let w = self.new_wire(modulus);
        let w1 = downcast_wire(w1);
        self.out.rel(format!(
            "  ${} <- @addc({}: ${}, <{}>);",
            w.opaque_value,
            ModulusFieldName(modulus),
            w1.opaque_value,
            c2
        ));
        upcast_wire(w)
    }

    fn assert_zero(&self, m: &NatType, w1: &Wire) {
        let w1 = downcast_wire(w1);
        self.out
            .rel(format!("  @assert_zero({}: ${});", ModulusFieldName(m), w1.opaque_value));
    }

    fn assert_eq(&self, _m1: &NatType, w1: &Wire, _m2: &NatType, w2: &Wire) {
        let w1 = downcast_wire(w1);
        let w2 = downcast_wire(w2);
        self.out.rel(format!(
            "  @assert_equal(${}; ${});",
            w1.opaque_value, w2.opaque_value
        ));
    }

    fn assert_eq_scalar_vec(&self, _m1: &NatType, w1: &Wire, _m2: &NatType, wires: Vec<Wire>) {
        let w1 = downcast_wire(w1);
        self.out.rel(format!(
            "  @assert_equal(${}; {});",
            w1.opaque_value,
            wire_list_to_string(wires)
        ));
    }

    fn add_instance(&self, modulus: &NatType, x: &Value) {
        if CURR_DOMAIN >= Verifier {
            self.out.ins(modulus, format!(
                "  <{}>;",
                ZkscIntDisplay::new(modulus, x)
            ));
        }
    }

    fn add_witness(&self, modulus: &NatType, x: &Value) {
        if CURR_DOMAIN == Prover {
            self.out.wit(modulus, format!(
                "  <{}>;",
                ZkscIntDisplay::new(modulus, x)
            ));
        }
    }

    fn get_instance(&self, m: &NatType) -> Wire {
        let w = self.new_wire(m);
        self.out
            .rel(format!("  ${} <- @public({});", w.opaque_value, ModulusFieldName(m)));
        upcast_wire(w)
    }

    fn get_witness(&self, m: &NatType) -> Wire {
        let w = self.new_wire(m);
        self.out
            .rel(format!("  ${} <- @private({});", w.opaque_value, ModulusFieldName(m)));
        upcast_wire(w)
    }

    fn get_instance_wr(&self, m: &NatType, n: usize) -> WireRange {
        let wr = self.new_wire_range(m, n);
        if n > 0 {
            self.out
                .rel(format!("  {} <- @public({});", WR(&wr), ModulusFieldName(m)));
        }
        upcast_wr(wr)
    }

    fn get_witness_wr(&self, m: &NatType, n: usize) -> WireRange {
        let wr = self.new_wire_range(m, n);
        if n > 0 {
            self.out
                .rel(format!("  {} <- @private({});", WR(&wr), ModulusFieldName(m)));
        }
        upcast_wr(wr)
    }

    fn flush(&self) {
        self.out.flush();
    }

    fn bool2int(&self, input_modulus: &NatType, w1: &Wire, output_modulus: &NatType) -> Wire {
        if input_modulus == output_modulus {
            bitwise_copy_wire(w1)
        } else {
            let w = self.new_wire(output_modulus);
            let w1 = downcast_wire(w1);
            self.out.rel(format!(
                "  {}: ${} <- @convert({}: ${}, @modulus)",
                ModulusFieldName(output_modulus),
                w.opaque_value,
                ModulusFieldName(input_modulus),
                w1.opaque_value,
            ));
            upcast_wire(w)
        }
    }

    fn int_field_switch(&self, input_modulus: &NatType, w1: &Wire, output_modulus: &NatType) -> Wire {
        if input_modulus == output_modulus {
            bitwise_copy_wire(w1)
        } else {
            let w = self.new_wire(output_modulus);
            let w1 = downcast_wire(w1);
            self.out.rel(format!(
                "  {}: ${} <- @convert({}: ${}, @modulus)",
                ModulusFieldName(output_modulus),
                w.opaque_value,
                ModulusFieldName(input_modulus),
                w1.opaque_value,
            ));
            upcast_wire(w)
        }
    }

    fn begin_function(&self, sieve_fn: &String, output_moduli: &Vec<&NatType>, input_moduli: Vec<&NatType>) -> (Vec<Wire>, usize) {
        assert!(!*self.in_function.borrow());
        *self.in_function.borrow_mut() = true;
        // save global wire number
        *self.saved_next_wire.borrow_mut() = *self.next_wire.borrow();
        // wire numbers start from 0 in each function
        *self.next_wire.borrow_mut() = 0;
        let uid0 = *self.saved_next_wire.borrow();
        let sieve_fn_name: String = format!("{}_{}", sieve_fn, uid0);
        let uid = self.new_function_uid(sieve_fn_name.clone());

        let mut s: String = format!("  @function({}", sieve_fn_name);
        if output_moduli.len() > 0 {
            s.push_str(&format!(", @out: {}", moduli_to_string(output_moduli, 1)));
        }
        if input_moduli.len() > 0 {
            s.push_str(&format!(", @in: {}", moduli_to_string(&input_moduli, 1))); 
        }
        s.push_str(")");
        self.out.rel(s);
        self.out.set_indent("  ");
        let output_wires = output_moduli.iter().map(|m| self.new_wire(m)).collect();
        let input_wires = input_moduli.iter().map(|m| self.new_wire(m)).collect();
        let output_moduli = output_moduli.iter().map(|m| ModulusFieldName(m).to_string()).collect();
        *self.fn_outputs.borrow_mut() = (output_moduli, output_wires);
        (upcast_wires(input_wires), uid)
    }

    fn end_function(&self, wires_res: Vec<WireOrConst>) {
        assert!(*self.in_function.borrow());
        let mut output_moduli = Vec::new();
        output_moduli.append(&mut self.fn_outputs.borrow_mut().0);
        let mut wires_out = Vec::new();
        wires_out.append(&mut self.fn_outputs.borrow_mut().1);
        wires_out.into_iter().zip(wires_res.into_iter()).zip(output_moduli.iter()).for_each(|((w_out, w_res), m)| self.assign_woc(m, &w_out, &w_res));
        self.out.set_indent("");
        self.out.rel("  @end".to_string());

        // restore global wire number
        *self.next_wire.borrow_mut() = *self.saved_next_wire.borrow();
        *self.in_function.borrow_mut() = false;
    }

    fn create_vector(&self, m: &NatType, wocs: Vec<WireOrConst>) -> WireRange {
        let n = wocs.len();
        let wr = self.new_wire_range(m, n);
        self._declare_new_wire_range(&wr.alloc.to_allocation_impl());
        for i in 0 .. n {
            let w = wr.index(i);
            self.assign_woc(&ModulusFieldName(m).to_string(), &w, &wocs[i]);
        }
        upcast_wr(wr)
    }

    fn apply(&self, sieve_fn: usize, output_moduli: Vec<&NatType>, wires: Vec<&Wire>) -> Vec<Wire> {
        let sieve_fn = self.function_name(sieve_fn);
        let wires = downcast_wires(wires);
        let output_wires: Vec<_> = output_moduli.iter().map(|m| self.new_wire(m)).collect();
        let mut s: String = "  ".to_string();
        for i in 0 .. output_wires.len() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&format!("${}", output_wires[i].opaque_value));
            if i + 1 == output_wires.len() {
                s.push_str(" <- ");
            }
        }
        s.push_str(&format!("@call({}", sieve_fn));
        for i in 0 .. wires.len() {
            s.push_str(&format!(", ${}", wires[i].opaque_value));
        }
        s.push_str(");");
        self.out.rel(s);
        upcast_wires(output_wires)
    }

    fn switch_apply(&self, sieve_fns: &Vec<usize>, default_sieve_fn: usize, ints: &Vec<Integer>, w_modulus: &NatType,
                    output_moduli: Vec<&NatType>, input_moduli: Vec<&NatType>, w: &Wire, wires: Vec<&Wire>, witness_count: u64) -> Vec<Wire> {
        let sieve_fns: Vec<String> = sieve_fns.iter().map(|f| self.function_name(*f)).collect();
        let default_sieve_fn = self.function_name(default_sieve_fn);
        let first_wire = *self.next_wire.borrow();
        let fname = format!("switch_{}_{}", sieve_fns[0], first_wire);
        let uid = self.new_function_uid(fname.clone());
        let mut s: String = format!("  @function({}", fname);
        if output_moduli.len() > 0 {
            s.push_str(&format!(", @out: {}", moduli_to_string(&output_moduli, 1)));
        }
        let mut all_input_moduli = Vec::new();
        all_input_moduli.push(w_modulus);
        for m in input_moduli {
            all_input_moduli.push(m);
        }
        s.push_str(&format!(", @in: {}", moduli_to_string(&all_input_moduli, 1)));
        s.push_str(")");
        self.out.rel(s);
        self.out.rel("    @plugin(disjunction_v0, switch, permissive".to_string());
        for (s, i) in sieve_fns.iter().zip(ints.iter()) {
            self.out.rel(format!("      {}, {},", i, s));
        }
        self.out.rel(format!("      0, {},", default_sieve_fn));
        if output_moduli.len() > 0 {
            self.out.rel(format!("      @private({}:{})", ModulusFieldName(output_moduli[0]), witness_count));
        } else {
            self.out.rel(format!("      @private(0:{})", witness_count));
        }
        self.out.rel("    );".to_string());
        let mut all_input_wires = Vec::new();
        all_input_wires.push(w);
        for w in wires {
            all_input_wires.push(w);
        }
        self.apply(uid, output_moduli, all_input_wires)
    }

    fn vectorized_apply(&self, sieve_fn: usize, output_moduli: Vec<&NatType>, input_moduli: Vec<&NatType>, env_moduli: &Vec<NatType>, env_wires: Vec<&Wire>, wrs: Vec<&WireRange>) -> Vec<WireRange> {
        let sieve_fn = self.function_name(sieve_fn);
        let env_wires = downcast_wires(env_wires);
        let wrs = downcast_wrs(wrs);
        let n = wrs[0].length;
        let first_wire = *self.next_wire.borrow();
        let output_wrs: Vec<_> = output_moduli.iter().map(|m| self.new_wire_range(m, n)).collect();
        if n > 0 {
            let mut s: String = format!("  @function(map_{}_{}", sieve_fn, first_wire);
            if output_moduli.len() > 0 {
                s.push_str(&format!(", @out: {}", moduli_to_string(&output_moduli, n)));
            }
            s.push_str(&format!(", @in: {}{}{})",
                                 moduli_to_string(&env_moduli.iter().collect(), 1),
                                 if !env_moduli.is_empty() && !input_moduli.is_empty() { ", " } else { "" },
                                 moduli_to_string(&input_moduli, n)));
            self.out.rel(s);
            self.out.rel(format!("    @plugin(iter_v0, map, {}, {}, {});", sieve_fn, env_wires.len(), n));
            let mut s: String = "  ".to_string();
            for i in 0 .. output_wrs.len() {
                if i > 0 {
                    s.push_str(", ");
                }
                s.push_str(&WR(&output_wrs[i]).to_string());
                if i + 1 == output_wrs.len() {
                    s.push_str(" <- ");
                }
            }
            s.push_str(&format!("@call(map_{}_{}", sieve_fn, first_wire));
            for i in 0 .. env_wires.len() {
                s.push_str(&format!(", ${}", env_wires[i].opaque_value));
            }
            for i in 0 .. wrs.len() {
                s.push_str(&format!(", {}", WR(wrs[i])));
            }
            s.push_str(");");
            self.out.rel(s);
        }
        upcast_wrs(output_wrs)
    }

    fn plugin_apply(&self, plugin: &str, operation: &str, params: Vec<&str>, modulus: &NatType, num_outputs: usize, input_wires: Vec<&Wire>) -> Vec<Wire> {
        let input_wires = downcast_wires(input_wires);
        let first_wire = *self.next_wire.borrow();
        let mut output_moduli = Vec::new();
        for _ in 0 .. num_outputs {
            output_moduli.push(modulus);
        }
        let mut input_moduli = Vec::new();
        for _ in 0 .. input_wires.len() {
            input_moduli.push(modulus);
        }
        let output_wires: Vec<_> = output_moduli.iter().map(|m| self.new_wire(m)).collect();
        let fname: String = format!("plugin_{}_{}_{}", plugin, operation, first_wire);
        let mut s: String = format!("  @function({}", fname);
        if output_moduli.len() > 0 {
            s.push_str(&format!(", @out: {}", moduli_to_string(&output_moduli, 1)));
        }
        if input_moduli.len() > 0 {
            s.push_str(&format!(", @in: {})", moduli_to_string(&input_moduli, 1)));
        }
        self.out.rel(s);
        s = format!("    @plugin({}, {}", plugin, operation);
        for param in params {
            s.push_str(&format!(", {}", param));
        }
        s.push_str(");");
        self.out.rel(s);
        let mut s: String = "  ".to_string();
        for i in 0 .. output_wires.len() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&format!("${}", output_wires[i].opaque_value));
            if i + 1 == output_wires.len() {
                s.push_str(" <- ");
            }
        }
        s.push_str(&format!("@call({}", fname));
        for i in 0 .. input_wires.len() {
            s.push_str(&format!(", ${}", input_wires[i].opaque_value));
        }
        s.push_str(");");
        self.out.rel(s);
        upcast_wires(output_wires)
    }

    fn plugin_apply_wr(&self, plugin: &str, operation: &str, params: Vec<&str>, modulus: &NatType, output_counts: Vec<usize>, input_wrs: Vec<&WireRange>) -> Vec<WireRange> {
        let input_wrs = downcast_wrs(input_wrs);
        let first_wire = *self.next_wire.borrow();
        let mut output_moduli = Vec::new();
        for _ in 0 .. output_counts.len() {
            output_moduli.push(modulus);
        }
        let mut input_moduli = Vec::new();
        for _ in 0 .. input_wrs.len() {
            input_moduli.push(modulus);
        }
        let output_wrs: Vec<_> = output_counts.iter().map(|n| self.new_wire_range(modulus, *n)).collect();
        let fname: String = format!("plugin_{}_{}_{}", plugin, operation, first_wire);
        let mut s: String = format!("  @function({}", fname);
        if output_moduli.len() > 0 {
            s.push_str(&format!(", @out: {}", moduli_and_counts_to_string(&output_moduli, &output_counts)));
        }
        let input_counts = input_wrs.iter().map(|wr| wr.length).collect();
        if input_moduli.len() > 0 {
            s.push_str(&format!(", @in: {})", moduli_and_counts_to_string(&input_moduli, &input_counts)));
        }
        self.out.rel(s);
        s = format!("    @plugin({}, {}", plugin, operation);
        for param in params {
            s.push_str(&format!(", {}", param));
        }
        s.push_str(");");
        self.out.rel(s);
        let mut s: String = "  ".to_string();
        for i in 0 .. output_wrs.len() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&format!("{}", WR(&output_wrs[i])));
            if i + 1 == output_wrs.len() {
                s.push_str(" <- ");
            }
        }
        s.push_str(&format!("@call({}", fname));
        for i in 0 .. input_wrs.len() {
            s.push_str(&format!(", {}", WR(input_wrs[i])));
        }
        s.push_str(");");
        self.out.rel(s);
        upcast_wrs(output_wrs)
    }

    fn get_next_wire_number(&self) -> u64 {
        *self.next_wire.borrow()
    }

    fn get_rel_file_size(&self) -> u64 {
        self.out.get_rel_size()
    }

    fn finalize(&self) {
        self.out.finalize();
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
    let output = Rc::new(RefCell::new(BufWriter::new(io::stdout())));
    // The order of operations here is important, it must be
    //   1. EmpChallengeBackend::new
    //   2. set_boxed_challenge_backend
    //   3. FilesIR0plus::new
    //   4. read_emp_line_1
    // Otherwise it can get into deadlock if challenges with EMP (--interactive) are used.
    let challenge_backend0 = OobChallengeBackend::new(Rc::clone(&output), &output_prefix);
    set_boxed_challenge_backend(Box::new(challenge_backend0));
    let sieve: Box<dyn SIEVEIR> = if output_prefix.is_empty() {
        Box::new(IR0plus::new(Box::new(StdoutIR0plus::new(output))))
    } else {
        Box::new(IR0plus::new(Box::new(FilesIR0plus::new(&output_prefix))))
    };
    challenge_backend().read_emp_line_1();
    set_boxed_sieve_backend(sieve);
    zksc_run(
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
    )
}
