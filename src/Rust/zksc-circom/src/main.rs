use std::any::Any;
use std::cell::RefCell;
use std::fs::File;
//use std::io;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Read;
use std::io::Write;
//use std::io::Stdout;
//use std::rc::Rc;

use num_traits::identities::Zero;
use simple_logger::SimpleLogger;

use zksc_app_lib::command_line::*;
use zksc_app_lib::*;
use zksc_app_lib::zksc_integer::ZkscIntDisplay;

const CIRCOM_VERSION: &str = "2.0.0";

#[derive(Clone, Debug)]
struct WireImpl(String);

impl WireTrait for WireImpl {
    fn to_any(&self) -> &dyn Any {
        self as &dyn Any
    }
}

impl WireImpl {
    fn new(wire: u64) -> WireImpl {
        WireImpl(format!("s{}", wire))
    }
}

#[derive(Clone, Debug)]
struct WireRangeImpl {
    name: String,
    first_index: usize, // slicing may change it from 0
    length: usize, // length of the slice, not the original wire range
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
    fn new(first_wire: u64, length: usize) -> WireRangeImpl {
        WireRangeImpl {
            name: format!("sa{}", first_wire),
            first_index: 0,
            length,
        }
    }

    fn index(&self, i: usize) -> WireImpl {
        assert!(i < self.length);
        WireImpl(format!("{}[{}]", self.name, self.first_index + i))
    }

    fn index_by_var(&self, x: &str) -> String {
        if self.first_index == 0 {
            format!("{}[{}]", self.name, x)
        } else {
            format!("{}[{} + {}]", self.name, self.first_index, x)
        }
    }
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

struct Function {
    name: String,
    num_ins: u64,
    num_wit: u64,
}

struct CircomBackend {
    rel: RefCell<BufWriter<File>>,
    funs: RefCell<BufWriter<File>>,
    ins: RefCell<BufWriter<File>>,
    wit: RefCell<BufWriter<File>>,
    prime: RefCell<BufWriter<File>>,
    indent: RefCell<String>,
    fun_indent: RefCell<String>,
    fun_body: RefCell<String>,
    next_wire: RefCell<u64>,
    num_ins: RefCell<u64>,
    num_wit: RefCell<u64>,
    fun_num_ins: RefCell<u64>,
    fun_num_wit: RefCell<u64>,
    funs_filename: String,
    ins_filename: String,
    modulus_fixed: RefCell<bool>,
    modulus_tag: RefCell<u64>,
    modulus_bigint: RefCell<Integer>,
    is_inside_fn_def: RefCell<bool>,
    defined_funs: RefCell<Vec<Function>>,
}

impl CircomBackend {
    fn new(prefix: &str) -> CircomBackend {
        let rel = RefCell::new(BufWriter::new(File::create(prefix.to_owned() + ".circom").expect("Failed to open file for writing")));
        let funs_filename = prefix.to_owned() + "_funs.circom";
        let funs = RefCell::new(BufWriter::new(File::create(&funs_filename).expect("Failed to open file for writing")));
        let ins_filename = prefix.to_owned() + "_verifier_input.json";
        let ins = RefCell::new(BufWriter::new(File::create(&ins_filename).expect("Failed to open file for writing")));
        let wit = RefCell::new(BufWriter::new(File::create(prefix.to_owned() + "_prover_input.json").expect("Failed to open file for writing")));
        let prime = RefCell::new(BufWriter::new(File::create(prefix.to_owned() + "_prime.txt").expect("Failed to open file for writing")));
        let indent = RefCell::new("    ".to_string());
        let fun_indent = RefCell::new("".to_string());
        let fun_body = RefCell::new("".to_string());
        let defined_funs = RefCell::new(Vec::new());
        if NEED_REL {
            writeln!(rel.borrow_mut(), "pragma circom {};", CIRCOM_VERSION).expect("");
            writeln!(rel.borrow_mut(), "").expect("");
            writeln!(rel.borrow_mut(), "template Main (num_wit, num_ins) {{").expect("");
            writeln!(rel.borrow_mut(), "{}signal input wit[num_wit];", indent.borrow()).expect("");
            writeln!(rel.borrow_mut(), "{}signal input ins[num_ins];", indent.borrow()).expect("");
            writeln!(rel.borrow_mut(), "{}var wi = 0;", indent.borrow()).expect("");
            writeln!(rel.borrow_mut(), "{}var ii = 0;", indent.borrow()).expect("");
        }
        if CURR_DOMAIN >= Verifier {
            writeln!(ins.borrow_mut(), "[").expect("");
        }
        if CURR_DOMAIN == Prover {
            writeln!(wit.borrow_mut(), "{{").expect("");
            writeln!(wit.borrow_mut(), "\"wit\":").expect("");
            writeln!(wit.borrow_mut(), "[").expect("");
        }
        CircomBackend {
            rel, funs, ins, wit, prime, indent, fun_indent, fun_body,
            next_wire: RefCell::new(0),
            num_ins: RefCell::new(0),
            num_wit: RefCell::new(0),
            fun_num_ins: RefCell::new(0),
            fun_num_wit: RefCell::new(0),
            funs_filename,
            ins_filename,
            modulus_fixed: RefCell::new(false),
            modulus_tag: RefCell::new(0),
            modulus_bigint: RefCell::new(Integer::zero()),
            is_inside_fn_def: RefCell::new(false),
            defined_funs,
        }
    }

    fn inside_fn_def(&self) -> bool {
        *self.is_inside_fn_def.borrow()
    }

    fn check_modulus(&self, m: &NatType) {
        if *self.modulus_fixed.borrow() {
            let m_modulus = m.modulus.clone().expect("Infinite modulus not supported in $post");
            assert_eq!(*self.modulus_tag.borrow(), m.tag, "Circom backend does not support multiple moduli: {} and {} used", self.modulus_bigint.borrow(), m_modulus);
        } else {
            *self.modulus_fixed.borrow_mut() = true;
            *self.modulus_tag.borrow_mut() = m.tag;
            let m = m.modulus.clone().expect("Infinite modulus not supported in $post");
            let m_bn128 = Integer::parse_bytes(b"30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001", 16).unwrap();
            let m_bls12381 = Integer::parse_bytes(b"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001", 16).unwrap();
            let p: &str = if &m == &m_bn128 {
                "bn128"
            } else if &m == &m_bls12381 {
                "bls12381"
            } else {
                panic!("Modulus {} not supported by the circom backend (because snarkjs does not support it). Only the moduli {} and {} are supported.", m, m_bn128, m_bls12381);
            };
            writeln!(self.prime.borrow_mut(), "{}", p).expect("");
            *self.modulus_bigint.borrow_mut() = m;
        }
    }

    fn new_wire_0(&self) -> WireImpl {
        let w = *self.next_wire.borrow();
        *self.next_wire.borrow_mut() = w + 1;
        WireImpl::new(w)
    }

    fn new_wire(&self, m: &NatType) -> WireImpl {
        self.check_modulus(m);
        self.new_wire_0()
    }

    fn new_wire_range(&self, m: &NatType, n: usize) -> WireRangeImpl {
        self.check_modulus(m);
        let w = *self.next_wire.borrow();
        *self.next_wire.borrow_mut() = w + n as u64;
        let wr = WireRangeImpl::new(w, n);
        self.rel(format!("signal {}[{}];", wr.name, wr.length));
        wr
    }

    // copy n values from the instance stream to a new signal array
    // return the string to be added to the arguments to pass this witness array to a function
    fn copy_instance(&self, n: u64) -> String {
        if n == 0 {
            String::new()
        } else {
            let w = *self.next_wire.borrow();
            *self.next_wire.borrow_mut() = w + 1;
            let name = format!("ins{}", w);
            self.rel(format!("signal {}[{}];", &name, n));
            self.rel(format!("for (var i = 0; i < {}; i++) {{", n));
            self.rel(format!("    {}[i] <== ins[ii];", &name));
            self.rel(format!("    ii++;"));
            self.rel(format!("}}"));
            name
        }
    }

    // copy n values from the witness stream to a new signal array
    // return the string to be added to the arguments to pass this witness array to a function
    fn copy_witness(&self, n: u64) -> String {
        if n == 0 {
            String::new()
        } else {
            let w = *self.next_wire.borrow();
            *self.next_wire.borrow_mut() = w + 1;
            let name = format!("wit{}", w);
            self.rel(format!("signal {}[{}];", &name, n));
            self.rel(format!("for (var i = 0; i < {}; i++) {{", n));
            self.rel(format!("    {}[i] <== wit[wi];", &name));
            self.rel(format!("    wi++;"));
            self.rel(format!("}}"));
            name
        }
    }

    fn copy_instance_arr(&self, wr_len: usize, n: u64, i: &str) -> String {
        if n == 0 {
            String::new()
        } else {
            let w = *self.next_wire.borrow();
            *self.next_wire.borrow_mut() = w + 1;
            let name = format!("ins{}", w);
            self.rel(format!("signal {}[{}][{}];", &name, wr_len, n));
            self.rel(format!("for (var j = 0; j < {}; j++) {{", wr_len));
            self.rel(format!("    for (var i = 0; i < {}; i++) {{", n));
            self.rel(format!("        {}[j][i] <== ins[ii];", &name));
            self.rel(format!("        ii++;"));
            self.rel(format!("    }}"));
            self.rel(format!("}}"));
            format!("{}[{}]", name, i)
        }
    }

    fn copy_witness_arr(&self, wr_len: usize, n: u64, i: &str) -> String {
        if n == 0 {
            String::new()
        } else {
            let w = *self.next_wire.borrow();
            *self.next_wire.borrow_mut() = w + 1;
            let name = format!("wit{}", w);
            self.rel(format!("signal {}[{}][{}];", &name, wr_len, n));
            self.rel(format!("for (var j = 0; j < {}; j++) {{", wr_len));
            self.rel(format!("    for (var i = 0; i < {}; i++) {{", n));
            self.rel(format!("        {}[j][i] <== wit[wi];", &name));
            self.rel(format!("        wi++;"));
            self.rel(format!("    }}"));
            self.rel(format!("}}"));
            format!("{}[{}]", name, i)
        }
    }

    fn rel(&self, s: String) {
        if self.inside_fn_def() {
            self.fun_body.borrow_mut().push_str(&format!("{}{}\n", self.fun_indent.borrow(), s));
        } else {
            writeln!(self.rel.borrow_mut(), "{}{}", self.indent.borrow(), s).expect("");
        }
    }

    fn funs(&self, s: String) {
        writeln!(self.funs.borrow_mut(), "{}{}", self.fun_indent.borrow(), s).expect("");
    }

    fn ins(&self, s: String) {
        writeln!(self.ins.borrow_mut(), "{}", s).expect("");
    }

    fn wit(&self, s: String) {
        writeln!(self.wit.borrow_mut(), "{}", s).expect("");
    }

    fn set_indent(&self, s: &str) {
        *self.indent.borrow_mut() = s.to_string();
    }

    fn set_fun_indent(&self, s: &str) {
        *self.fun_indent.borrow_mut() = s.to_string();
    }
}

impl SIEVEIR for CircomBackend {
    fn zero_wire(&self, _: &NatType) -> Wire { todo!() }

    fn clone_wire(&self, w: &Wire) -> Wire {
        let w = downcast_wire(w);
        upcast_wire(w.clone())
    }

    fn drop_wire(&self, _: &mut Wire) {}

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
        let wr2 = WireRangeImpl {
            name: wr.name.clone(),
            first_index: wr.first_index + ir.first,
            length: ir.length,
        };
        upcast_wr(wr2)
    }

    fn wire_to_wire_range(&self, _w: &Wire) -> WireRange { todo!() }

    fn and(&self, _: &NatType, _: &Wire, _: &Wire) -> Wire { todo!() }
    fn xor(&self, _: &NatType, _: &Wire, _: &Wire) -> Wire { todo!() }
    fn not(&self, _: &NatType, _: &Wire) -> Wire { todo!() }
    fn const_bool(&self, _: &NatType, _: bool) -> Wire { todo!() }

    fn mul(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        let w2 = downcast_wire(w2);
        self.rel(format!("signal {} <== {} * {};", w.0, w1.0, w2.0));
        upcast_wire(w)
    }

    fn add(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        let w2 = downcast_wire(w2);
        self.rel(format!("signal {} <== {} + {};", w.0, w1.0, w2.0));
        upcast_wire(w)
    }

    fn mulc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        self.rel(format!("signal {} <== {} * {};", w.0, c2, w1.0));
        upcast_wire(w)
    }

    fn addc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let w = self.new_wire(m);
        let w1 = downcast_wire(w1);
        self.rel(format!("signal {} <== {} + {};", w.0, w1.0, c2));
        upcast_wire(w)
    }

    fn assert_zero(&self, _: &NatType, w1: &Wire) {
        let w1 = downcast_wire(w1);
        self.rel(format!("{} === 0;", w1.0));
    }

    fn begin_function(&self, sieve_fn: &String, _output_moduli: &Vec<&NatType>, input_moduli: Vec<&NatType>) -> (Vec<Wire>, usize) {
        assert!(!self.inside_fn_def());
        *self.is_inside_fn_def.borrow_mut() = true;
        *self.fun_num_ins.borrow_mut() = 0;
        *self.fun_num_wit.borrow_mut() = 0;
        let sieve_fn = format!("{}_{}", sieve_fn, self.defined_funs.borrow().len());
        self.funs(format!(""));
        self.funs(format!("template {} () {{", &sieve_fn));
        self.fun_body.borrow_mut().clear();
        self.set_fun_indent("    ");
        let input_wires: Vec<_> = input_moduli.into_iter().map(|m| {
            let w = self.new_wire(m);
            self.rel(format!("signal input {};", w.0));
            upcast_wire(w)
        }).collect();
        self.defined_funs.borrow_mut().push(Function {
            name: sieve_fn,
            num_ins: 0,
            num_wit: 0,
        });
        (input_wires, self.defined_funs.borrow().len() - 1)
    }

    fn end_function(&self, wires_res: Vec<WireOrConst>) {
        assert!(self.inside_fn_def());
        let num_wit = *self.fun_num_wit.borrow();
        let num_ins = *self.fun_num_ins.borrow();
        if num_wit > 0 {
            self.funs(format!("signal input wit[{}];", num_wit));
            self.funs(format!("var wi = 0;"));
        }
        if num_ins > 0 {
            self.funs(format!("signal input ins[{}];", num_ins));
            self.funs(format!("var ii = 0;"));
        }
        for woc in wires_res {
            let w = self.new_wire_0();
            match woc {
                WireOrConst::W(w1) => {
                    self.rel(format!("signal output {} <== {};", w.0, downcast_wire(w1).0));
                }
                WireOrConst::C(c1) => {
                    self.rel(format!("signal output {} <== {};", w.0, c1));
                }
            }
        }
        self.set_fun_indent("");
        self.funs(format!("{}}}", self.fun_body.borrow()));
        self.fun_body.borrow_mut().clear();
        let uid = self.defined_funs.borrow().len() - 1;
        self.defined_funs.borrow_mut()[uid].num_wit = num_wit;
        self.defined_funs.borrow_mut()[uid].num_ins = num_ins;
        *self.is_inside_fn_def.borrow_mut() = false;
    }

    fn create_vector(&self, m: &NatType, wocs: Vec<WireOrConst>) -> WireRange {
        let n = wocs.len();
        let wr = self.new_wire_range(m, n);
        for i in 0 .. n {
            let w = wr.index(i);
            match &wocs[i] {
                WireOrConst::W(w1) => {
                    self.rel(format!("{} <== {};", w.0, downcast_wire(w1).0));
                }
                WireOrConst::C(c1) => {
                    self.rel(format!("{} <== {};", w.0, c1));
                }
            }
        }
        upcast_wr(wr)
    }

    fn apply(&self, sieve_fn: usize, output_moduli: Vec<&NatType>, input_wires: Vec<&Wire>) -> Vec<Wire> {
        let fun: &Function = &self.defined_funs.borrow()[sieve_fn];
        let input_wires = downcast_wires(input_wires);
        let output_wires: Vec<_> = output_moduli.iter().map(|m| self.new_wire(m)).collect();
        let mut inputs: String = self.copy_witness(fun.num_wit);
        let copied_ins = self.copy_instance(fun.num_ins);
        if inputs.len() > 0 && copied_ins.len() > 0 {
            inputs.push_str(", ");
        }
        inputs.push_str(&copied_ins);
        for w in input_wires {
            if inputs.len() > 0 {
                inputs.push_str(", ");
            }
            inputs.push_str(&w.0);
        }
        let mut outputs: String = String::new();
        for w in &output_wires {
            if outputs.len() > 0 {
                outputs.push_str(", ");
            }
            outputs.push_str(&w.0);
        }
        let call_str = format!("{}()({})", fun.name, inputs);
        if output_wires.len() == 0 {
            self.rel(format!("{};", call_str));
        } else if output_wires.len() == 1 {
            self.rel(format!("signal {} <== {};", outputs, call_str));
        } else {
            self.rel(format!("signal {};", outputs));
            self.rel(format!("({}) <== {};", outputs, call_str));
        }
        upcast_wires(output_wires)
    }

    fn vectorized_apply(&self, sieve_fn: usize, output_moduli: Vec<&NatType>, _input_moduli: Vec<&NatType>, _env_moduli: &Vec<NatType>, env_wires: Vec<&Wire>, input_wrs: Vec<&WireRange>) -> Vec<WireRange> {
        let fun: &Function = &self.defined_funs.borrow()[sieve_fn];
        let env_wires = downcast_wires(env_wires);
        let input_wrs = downcast_wrs(input_wrs);
        let n = input_wrs[0].length;
        let output_wrs: Vec<_> = output_moduli.iter().map(|m| self.new_wire_range(m, n)).collect();
        let mut inputs: String = self.copy_witness_arr(n, fun.num_wit, "i");
        let copied_ins = self.copy_instance_arr(n, fun.num_ins, "i");
        if inputs.len() > 0 && copied_ins.len() > 0 {
            inputs.push_str(", ");
        }
        inputs.push_str(&copied_ins);
        for w in env_wires {
            if inputs.len() > 0 {
                inputs.push_str(", ");
            }
            inputs.push_str(&w.0);
        }
        for wr in input_wrs {
            if inputs.len() > 0 {
                inputs.push_str(", ");
            }
            inputs.push_str(&wr.index_by_var("i"));
        }
        let mut outputs: String = String::new();
        for wr in &output_wrs {
            if outputs.len() > 0 {
                outputs.push_str(", ");
            }
            outputs.push_str(&wr.index_by_var("i"));
        }
        self.rel(format!("for (var i = 0; i < {}; i++) {{", n));
        self.set_indent("        ");
        let call_str = format!("{}()({})", fun.name, inputs);
        if output_wrs.len() == 0 {
            self.rel(format!("{};", call_str));
        } else if output_wrs.len() == 1 {
            self.rel(format!("{} <== {};", outputs, call_str));
        } else {
            self.rel(format!("({}) <== {};", outputs, call_str));
        }
        self.set_indent("    ");
        self.rel(format!("}}"));
        upcast_wrs(output_wrs)
    }

    fn assert_eq_scalar_vec(&self, _: &NatType, _: &Wire, _: &NatType, _: Vec<Wire>) { todo!() }

    fn add_instance(&self, m: &NatType, x: &Value) {
        let ni = *self.num_ins.borrow();
        if CURR_DOMAIN >= Verifier {
            self.ins(format!("{}\"{}\"", if ni > 0 {","} else {""}, ZkscIntDisplay::new(m, x)));
        }
        *self.num_ins.borrow_mut() = ni + 1;
    }

    fn get_instance(&self, m: &NatType) -> Wire {
        let w = self.new_wire(m);
        self.rel(format!("signal {} <== ins[ii];", w.0));
        self.rel(format!("ii++;"));
        *self.fun_num_ins.borrow_mut() += 1;
        upcast_wire(w)
    }

    fn add_witness(&self, m: &NatType, x: &Value) {
        let nw = *self.num_wit.borrow();
        if CURR_DOMAIN == Prover {
            self.wit(format!("{}\"{}\"", if nw > 0 {","} else {""}, ZkscIntDisplay::new(m, x)));
        }
        *self.num_wit.borrow_mut() = nw + 1;
    }

    fn get_witness(&self, m: &NatType) -> Wire {
        let w = self.new_wire(m);
        self.rel(format!("signal {} <== wit[wi];", w.0));
        self.rel(format!("wi++;"));
        *self.fun_num_wit.borrow_mut() += 1;
        upcast_wire(w)
    }

    fn get_instance_wr(&self, m: &NatType, n: usize) -> WireRange {
        let wr = self.new_wire_range(m, n);
        self.rel(format!("for (var i = 0; i < {}; i++) {{", n));
        self.rel(format!("    {} <== ins[ii];", wr.index_by_var("i")));
        self.rel(format!("    ii++;"));
        self.rel(format!("}}"));
        upcast_wr(wr)
    }

    fn get_witness_wr(&self, m: &NatType, n: usize) -> WireRange {
        let wr = self.new_wire_range(m, n);
        self.rel(format!("for (var i = 0; i < {}; i++) {{", n));
        self.rel(format!("    {} <== wit[wi];", wr.index_by_var("i")));
        self.rel(format!("    wi++;"));
        self.rel(format!("}}"));
        upcast_wr(wr)
    }

    fn const_uint(&self, m: &NatType, x: &Value) -> Wire {
        let w = self.new_wire(m);
        self.rel(format!("signal {} <== {};", w.0, ZkscIntDisplay::new(m, x)));
        upcast_wire(w)
    }

    fn flush(&self) {
        self.rel.borrow_mut().flush().expect("");
        self.funs.borrow_mut().flush().expect("");
        self.ins.borrow_mut().flush().expect("");
        self.wit.borrow_mut().flush().expect("");
        self.prime.borrow_mut().flush().expect("");
    }

    fn finalize(&self) {
        if NEED_REL {
            if *self.num_ins.borrow() == 0 {
                // snarkjs requires at least one instance value
                self.ins(format!("\"0\""));
                *self.num_ins.borrow_mut() = 1;
            }
            self.set_indent("");
            self.rel("}".to_string());

            // Copy the contents of the funs file to the rel file as well
            self.flush();
            let mut funs_ro = BufReader::new(File::open(&self.funs_filename).expect(""));
            let mut funs_contents = String::new();
            funs_ro.read_to_string(&mut funs_contents).expect("");
            write!(self.rel.borrow_mut(), "{}", funs_contents).expect("");

            self.rel("".to_string());
            self.rel(format!("component main {{public [ins]}} = Main({}, {});", self.num_wit.borrow(), self.num_ins.borrow()));
        }
        if CURR_DOMAIN >= Verifier {
            writeln!(self.ins.borrow_mut(), "]").expect("");
        }
        if CURR_DOMAIN == Prover {
            writeln!(self.wit.borrow_mut(), "],").expect("");
            writeln!(self.wit.borrow_mut(), "\"ins\":").expect("");

            // Copy the contents of the instance file to the witness file as well
            self.flush();
            let mut ins_ro = BufReader::new(File::open(&self.ins_filename).expect(""));
            let mut ins_contents = String::new();
            ins_ro.read_to_string(&mut ins_contents).expect("");
            write!(self.wit.borrow_mut(), "{}", ins_contents).expect("");

            writeln!(self.wit.borrow_mut(), "}}").expect("");
        }

        self.flush();
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
    //let output = Rc::new(RefCell::new(BufWriter::new(io::stdout())));
    let sieve: Box<dyn SIEVEIR> = if output_prefix.is_empty() {
        panic!("stdout output not implemented for zksc-circom, use -o with runrust to specify an output prefix");
    } else {
        Box::new(CircomBackend::new(&output_prefix))
    };
    set_boxed_sieve_backend(sieve);
    zksc_run(
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
    )
}
