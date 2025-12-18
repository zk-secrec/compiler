use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Read;
use std::io::Write;
use std::rc::Rc;

use num_traits::{One, ToPrimitive};
use num_traits::identities::Zero;
use simple_logger::SimpleLogger;

use zksc_app_lib::command_line::*;
use zksc_app_lib::*;


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
    first_index: usize,
    length: usize,
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

    fn to_string(&self) -> String {
        if self.first_index == 0 {
            self.name.clone()
        } else {
            //format!("({} + {})", self.name, self.first_index)
            format!("{}[{}]", self.name, self.first_index)
        }
    }
}

struct Function {
    name: String,
    num_cols: usize,  
}

pub(crate) struct ZKSCAIRIMPL {
    src_output: Rc<RefCell<BufWriter<File>>>,
    fun_output: Rc<RefCell<BufWriter<File>>>,
    in_function: RefCell<bool>,
    next_wire: RefCell<u64>, 
    next_wire_fn_stack: RefCell<Vec<u64>>,  
    defined_funs: RefCell<Vec<Function>>,
    drop_enabled: bool
}

impl ZKSCAIRIMPL {
    pub fn new(src_output: Rc<RefCell<BufWriter<File>>>, fun_output: Rc<RefCell<BufWriter<File>>>) -> ZKSCAIRIMPL {
        ZKSCAIRIMPL{
            src_output,
            fun_output,
            in_function: RefCell::new(false),
            next_wire: RefCell::new(0),
            next_wire_fn_stack: RefCell::new(Vec::new()),
            defined_funs : RefCell::new(Vec::new()),
            drop_enabled: false
        }
    }

    fn new_wire_0(&self) -> WireImpl {
        
        if *self.in_function.borrow() && !self.next_wire_fn_stack.borrow().is_empty() {
            let stack_len = self.next_wire_fn_stack.borrow().len();
            let w = self.next_wire_fn_stack.borrow()[stack_len - 1];
            self.next_wire_fn_stack.borrow_mut()[stack_len - 1] = w + 1;
            WireImpl::new(w)
        } else {
            let w = *self.next_wire.borrow();
            *self.next_wire.borrow_mut() = w + 1;
            WireImpl::new(w)
        }
    }

    fn new_wire(&self, m: &NatType) -> WireImpl {
        let w = self.new_wire_0();
        w
    }

    fn new_wire_raw(&self, s : String) -> WireImpl {
        WireImpl(s)
    }

    fn flush(&self) {
        self.src_output.borrow_mut().flush().expect("");
        self.fun_output.borrow_mut().flush().expect("");
    }

    fn current_output(&self) -> &Rc<RefCell<BufWriter<File>>> {
        if *self.in_function.borrow() {
            &self.fun_output
        } else {
            &self.src_output
        }
    }

    fn set_writing_fn(&self,in_function : bool) {
        *self.in_function.borrow_mut() = in_function;
    }

    fn format_const(&self,b:&Integer) -> String {
        format!("{}",b)
    }

    fn field_to_identifier(&self,m: &NatType) -> String {
        "Var".to_string()
    }

    fn new_wire_range(&self, m: &NatType, n: usize) -> WireRangeImpl {
        let w = *self.next_wire.borrow();
        *self.next_wire.borrow_mut() = w + n as u64;
        let wr = WireRangeImpl::new(w, n);
        wr
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


fn value_to_bigint(m: &NatType, x: &Value) -> Integer {
    match x.view() {
        ValueView::Bool(b) => if *b { Integer::one() } else { Integer::zero() },
        ValueView::ZkscDefined() => { (m.to_bigint)(x) },
        _ => panic!("value_to_bigint didn't get bool or own type",)
    }
}

impl SIEVEIR for ZKSCAIRIMPL {
    /**
     *  Core Utils
     */
    fn write_headers(&self, _ns: &Vec<NatType>, _supported_conversions: Vec<(&NatType, &NatType)>, _supported_plugins: Vec<&str>) {
        self.set_writing_fn(true);
        writeln!(self.current_output().borrow_mut(),"use crate::function_scope::ScopedContext;").expect("");
        writeln!(self.current_output().borrow_mut(),"use crate::symbolic::Var;").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        self.set_writing_fn(false);

        writeln!(self.current_output().borrow_mut(),"use zkair::function_scope::ScopedContext;").expect("");
        writeln!(self.current_output().borrow_mut(),"use zkair::funs::*;").expect("");
        writeln!(self.current_output().borrow_mut(),"use zkair::symbolic::Var;").expect("");
        writeln!(self.current_output().borrow_mut(),"use zkair::air_gen::{{extract_and_print_constraints, generate_and_print_trace}};").expect("");
        writeln!(self.current_output().borrow_mut(),"use icicle_runtime::{{runtime, Device}};").expect("");
        writeln!(self.current_output().borrow_mut(),"use instant::Instant;").expect("");
        writeln!(self.current_output().borrow_mut(),"use std::env;").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        writeln!(self.current_output().borrow_mut(),"fn main() {{").expect("");
        writeln!(self.current_output().borrow_mut(),"    tracing_subscriber::fmt()").expect("");
        writeln!(self.current_output().borrow_mut(),"        .with_env_filter(\"info\")").expect("");
        writeln!(self.current_output().borrow_mut(),"        .init();").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        writeln!(self.current_output().borrow_mut(),"    let start_init = Instant::now();").expect("");
        writeln!(self.current_output().borrow_mut(),"    let force_cpu = env::var(\"USE_CPU\").is_ok();").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        writeln!(self.current_output().borrow_mut(),"    let device = if force_cpu {{").expect("");
        writeln!(self.current_output().borrow_mut(),"        let cpu_device = Device::new(\"CPU\", 0);").expect("");
        writeln!(self.current_output().borrow_mut(),"        runtime::set_device(&cpu_device).expect(\"Failed to set CPU device\");").expect("");
        writeln!(self.current_output().borrow_mut(),"        cpu_device").expect("");
        writeln!(self.current_output().borrow_mut(),"    }} else {{").expect("");
        writeln!(self.current_output().borrow_mut(),"        let _ = icicle_runtime::load_backend_from_env_or_default();").expect("");
        writeln!(self.current_output().borrow_mut(),"        let cuda_device = Device::new(\"CUDA\", 0);").expect("");
        writeln!(self.current_output().borrow_mut(),"        let cpu_device = Device::new(\"CPU\", 0);").expect("");
        writeln!(self.current_output().borrow_mut(),"        if runtime::is_device_available(&cuda_device) {{").expect("");
        writeln!(self.current_output().borrow_mut(),"            runtime::set_device(&cuda_device).expect(\"Failed to set CUDA device\");").expect("");
        writeln!(self.current_output().borrow_mut(),"            cuda_device").expect("");
        writeln!(self.current_output().borrow_mut(),"        }} else {{").expect("");
        writeln!(self.current_output().borrow_mut(),"            runtime::set_device(&cpu_device).expect(\"Failed to set CPU device\");").expect("");
        writeln!(self.current_output().borrow_mut(),"            cpu_device").expect("");
        writeln!(self.current_output().borrow_mut(),"        }}").expect("");
        writeln!(self.current_output().borrow_mut(),"    }};").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        writeln!(self.current_output().borrow_mut(),"    let init_time = start_init.elapsed();").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        writeln!(self.current_output().borrow_mut(),"    let start_circuit = Instant::now();").expect("");
        writeln!(self.current_output().borrow_mut(),"    let ctx = ScopedContext::new();").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
    }

    fn zero_wire(&self, _m: &NatType) -> Wire {
        upcast_wire(self.new_wire_0())
    }

    fn clone_wire(&self, w1: &Wire) -> Wire {
        let w = downcast_wire(w1);
        upcast_wire(w.clone())
    }

    fn finalize(&self) {
        writeln!(self.src_output.borrow_mut(),"").expect("");
        writeln!(self.src_output.borrow_mut(),"    let circuit_time = start_circuit.elapsed();").expect("");
        writeln!(self.src_output.borrow_mut(),"").expect("");
        writeln!(self.src_output.borrow_mut(),"    let start_summary = Instant::now();").expect("");
        writeln!(self.src_output.borrow_mut(),"    ctx.print_summary();").expect("");
        writeln!(self.src_output.borrow_mut(),"    let summary_time = start_summary.elapsed();").expect("");
        writeln!(self.src_output.borrow_mut(),"").expect("");
        writeln!(self.src_output.borrow_mut(),"    let start_trace = Instant::now();").expect("");
        writeln!(self.src_output.borrow_mut(),"    let num_rows = ctx.num_rows();").expect("");
        writeln!(self.src_output.borrow_mut(),"    generate_and_print_trace(ctx.inner_ctx(), num_rows);").expect("");
        writeln!(self.src_output.borrow_mut(),"    let trace_time = start_trace.elapsed();").expect("");
        writeln!(self.src_output.borrow_mut(),"").expect("");
        writeln!(self.src_output.borrow_mut(),"    let start_constraints = Instant::now();").expect("");
        writeln!(self.src_output.borrow_mut(),"    extract_and_print_constraints(ctx.inner_ctx());").expect("");
        writeln!(self.src_output.borrow_mut(),"    let constraints_time = start_constraints.elapsed();").expect("");
        writeln!(self.src_output.borrow_mut(),"").expect("");
        writeln!(self.src_output.borrow_mut(),"    println!(\"ICICLE device:{{}}\", device.get_device_type());").expect("");
        writeln!(self.src_output.borrow_mut(),"    println!(\"Backend init:{{:?}}\", init_time);").expect("");
        writeln!(self.src_output.borrow_mut(),"    println!(\"Circuit execution:{{:?}}\", circuit_time);").expect("");
        writeln!(self.src_output.borrow_mut(),"    println!(\"Summary generation:{{:?}}\", summary_time);").expect("");
        writeln!(self.src_output.borrow_mut(),"    println!(\"Trace generation:{{:?}}\", trace_time);").expect("");
        writeln!(self.src_output.borrow_mut(),"    println!(\"Constraint extraction:{{:?}}\", constraints_time);").expect("");
        writeln!(self.src_output.borrow_mut(),"}}").expect("");
        self.flush();
    }

    fn drop_wire(&self, wire: &mut Wire) {

        if self.drop_enabled {
            //function params get dropped while no longer in function. filtering all those as they get dropped automatically regardless
            let w = downcast_wire(wire);
            if !w.0.starts_with('w') {
                writeln!(self.current_output().borrow_mut(),"drop({});",w.0).expect("");
            }
        }
    }

    /**
     *  Bool[2] fns
     */

    fn and(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        todo!("bool[2] not supported");
    }

    fn xor(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        todo!("bool[2] not supported");
    }

    fn not(&self, m: &NatType, w1: &Wire) -> Wire {
        todo!("bool[2] not supported");
    }

    fn const_bool(&self, m: &NatType, b: bool) -> Wire {
        todo!("bool[2] not supported");
    }

    /**
     *  Arith[N] fns
     */

     fn const_uint(&self, m: &NatType, x: &Value) -> Wire {
        let w = self.new_wire_0();
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.constant({});",w.0,self.format_const(&value_to_bigint(m, x))).expect("");
        upcast_wire(w)
    }

    fn mul(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let w = self.new_wire_0();
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.mul({}, {});",w.0,downcast_wire(w1).0,downcast_wire(w2).0).expect("");
        upcast_wire(w)
    }

    fn add(&self, m: &NatType, w1: &Wire, w2: &Wire) -> Wire {
        let w = self.new_wire_0();
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.add({}, {});",w.0,downcast_wire(w1).0,downcast_wire(w2).0).expect("");
        upcast_wire(w)
    }

    fn mulc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let w = self.new_wire_0();
        let const_var = self.new_wire_0();
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.constant({});",const_var.0,self.format_const(c2)).expect("");
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.mul({}, {});",w.0,downcast_wire(w1).0,const_var.0).expect("");
        upcast_wire(w)
    }

    fn addc(&self, m: &NatType, w1: &Wire, c2: &Integer) -> Wire {
        let w = self.new_wire_0();
        let const_var = self.new_wire_0();
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.constant({});",const_var.0,self.format_const(c2)).expect("");
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.add({}, {});",w.0,downcast_wire(w1).0,const_var.0).expect("");
        upcast_wire(w)
    }

    fn assert_zero(&self, m: &NatType, w: &Wire) {
        writeln!(self.current_output().borrow_mut(),"    ctx.assert_zero({});",downcast_wire(w).0).expect("");
    }

    fn assert_eq_scalar_vec(&self, m1: &NatType, w1: &Wire, m2: &NatType, wires: Vec<Wire>) { todo!() }


    /**
     *  Instance/Witness fns
     */

    fn add_instance(&self, m: &NatType, x: &Value) {
        let b = value_to_bigint(m,x);
        writeln!(self.current_output().borrow_mut(),"    ctx.add_ins({});",b).expect("");
    }

    fn get_instance(&self, _m: &NatType) -> Wire {
        let w = self.new_wire(_m);
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.instance();",w.0).expect("");
        upcast_wire(w)
    }

    fn add_witness(&self, m: &NatType, x: &Value) {
        let b = value_to_bigint(m,x);
        writeln!(self.current_output().borrow_mut(),"    ctx.add_wit({});",b).expect("");
    }

    fn get_witness(&self, _m: &NatType) -> Wire {
        let w = self.new_wire(_m);
        writeln!(self.current_output().borrow_mut(),"    let {} = ctx.witness();",w.0).expect("");
        upcast_wire(w)
    }

    /**
     *  Function gates
     */

    /// Begin a SIEVE IR function definition.
    /// Returns wires corresponding to the inputs
    /// and a UID for the SIEVE IR function (which must be different each time begin_function is called).
    fn begin_function(&self, _sieve_fn: &String, _output_moduli: &Vec<&NatType>, _input_moduli: Vec<&NatType>) -> (Vec<Wire>, usize) {
        self.set_writing_fn(true);
        self.next_wire_fn_stack.borrow_mut().push(_input_moduli.len() as u64);

        let mut c = 0;
        let input_wires: Vec<_> = _input_moduli.into_iter().map(|m| {
            let w = self.new_wire_raw(format!("w{}",c));
            c = c+1;
            upcast_wire(w)
        }).collect();

        let comma = if input_wires.len() > 0 { ", " } else { ""};
        write!(self.current_output().borrow_mut(),"pub fn {} (ctx: &ScopedContext{}",_sieve_fn,comma).expect("");

        let args : Vec<_> = (0..input_wires.len()).into_iter().map(|i| {
            format!("w{}: Var",i)
        }).collect();

        writeln!(self.current_output().borrow_mut(),"{}) -> Vec<usize> {{",args.join(", ")).expect("");
        writeln!(self.current_output().borrow_mut(),"    const FN_NAME: &str = \"{}\";",_sieve_fn).expect("");
        writeln!(self.current_output().borrow_mut(),"    const NUM_COLS: usize = COLCOUNT_{};",_sieve_fn.to_uppercase()).expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        let param_list: Vec<_> = (0..input_wires.len()).into_iter().map(|i| format!("w{}",i)).collect();
        writeln!(self.current_output().borrow_mut(),"    let param_cols = ctx.begin_function_ctx(FN_NAME, NUM_COLS, &[{}]);",param_list.join(", ")).expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        for i in 0..input_wires.len() {
            writeln!(self.current_output().borrow_mut(),"    let local_w{} = Var::new(param_cols[{}]);",i,i).expect("");
        }
        writeln!(self.current_output().borrow_mut(),"").expect("");
        self.defined_funs.borrow_mut().push(Function{
            name : _sieve_fn.to_string(),
            num_cols: 0,
        });

        (input_wires, self.defined_funs.borrow().len() - 1)
    }

    fn end_function(&self, _wires_res: Vec<WireOrConst>) {
        let num_cols = self.next_wire_fn_stack.borrow_mut().pop()
            .expect("end_function called without matching begin_function");
        let func_idx = self.defined_funs.borrow().len() - 1;
        let func_name = self.defined_funs.borrow()[func_idx].name.clone();
        self.defined_funs.borrow_mut()[func_idx].num_cols = num_cols as usize;

        writeln!(self.current_output().borrow_mut(),"").expect("");

        if _wires_res.len() > 0 {
            let labels: Vec<_> = _wires_res.into_iter().map(|woc| {
                match woc {
                    WireOrConst::W(w1) => {
                        format!("{}.index",downcast_wire(w1).0)
                    }
                    WireOrConst::C(c1) => {
                        format!("ctx.constant({}).index",c1)
                    }
                }
            }).collect();
            writeln!(self.current_output().borrow_mut(),"    ctx.end_function_ctx(FN_NAME, &[{}])",labels.join(", ")).expect("");
        } else {
            writeln!(self.current_output().borrow_mut(),"    ctx.end_function_ctx(FN_NAME, &[])").expect("");
        }

        writeln!(self.current_output().borrow_mut(),"}}").expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");
        writeln!(self.current_output().borrow_mut(),"const COLCOUNT_{}: usize = {};", func_name.to_uppercase(), num_cols).expect("");
        writeln!(self.current_output().borrow_mut(),"").expect("");

        self.set_writing_fn(false);
    }

    fn apply(&self, _uid: usize, _output_moduli: Vec<&NatType>, _input_wires: Vec<&Wire>) -> Vec<Wire> {
        let fun: &Function = &self.defined_funs.borrow()[_uid];

        let input_labels : Vec<_> = _input_wires.into_iter().map(|w| {downcast_wire(&w).0.clone()}).collect();
        let call_rhs = format!("{}(&ctx, {})",fun.name,input_labels.join(", "));

        if _output_moduli.len() > 0 {
            let output_wires: Vec<_> = _output_moduli.into_iter().map(|m| {
                upcast_wire(self.new_wire(m))
            }).collect();

            writeln!(self.current_output().borrow_mut(),"    let result = {};",call_rhs).expect("");
            for (i, wire) in output_wires.iter().enumerate() {
                let w = downcast_wire(wire);
                writeln!(self.current_output().borrow_mut(),"    let {} = Var::new(result[{}]);",w.0,i).expect("");
            }

            output_wires
        } else {
            writeln!(self.current_output().borrow_mut(),"    {};",call_rhs).expect("");
            vec![]
        }
    }

    fn create_vector(&self, m: &NatType, wocs: Vec<WireOrConst>) -> WireRange {

        let wr = self.new_wire_range(m, wocs.len());

        let wocs_str: Vec<_> = wocs.into_iter().map(|woc| {
            match woc {
                WireOrConst::W(w1) => {
                    format!("{}",downcast_wire(w1).0)
                }
                WireOrConst::C(c1) => {
                    format!("ctx.constant({})",c1)
                }
            }
        }).collect();

        writeln!(self.current_output().borrow_mut(),"    let {} = vec![{}];",wr.name,wocs_str.join(", ")).expect("");


        upcast_wr(wr)
    }

    fn index_wire_range(&self, wr: &WireRange, i: usize) -> Wire {
        let w = self.new_wire_0();

        let w_i = downcast_wr(wr).index(i);

        writeln!(self.current_output().borrow_mut(),"    let {} = {};",w.0,w_i.0).expect("");

        upcast_wire(w)
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

    fn wire_to_wire_range(&self, _w: &Wire) -> WireRange {
        todo!()
    }

    fn clone_wire_range(&self, wr: &WireRange) -> WireRange {
        upcast_wr(downcast_wr(wr).clone())
    }

    fn vectorized_apply(&self, _uid: usize, _output_moduli: Vec<&NatType>, _input_moduli: Vec<&NatType>, _env_moduli: &Vec<NatType>, _env_wires: Vec<&Wire>, _wrs: Vec<&WireRange>) -> Vec<WireRange> {
        let n = _wrs[0].length();
        let fn_name = &self.defined_funs.borrow()[_uid].name;

        let mut out_wrs: Vec<_> = vec![];

        for i in 0.._output_moduli.len() {
            out_wrs.push(self.new_wire_range(_output_moduli[i], n));
        }

        let out_w = self.new_wire_0();
        let inner_vecs : Vec<_> = (0..out_wrs.len()).into_iter().map(|_| "vec![]").collect();
        writeln!(self.current_output().borrow_mut(),"    let mut {} : Vec<Vec<Var>> = vec![{}];",out_w.0,inner_vecs.join(", ")).expect("");
        let mut args = vec![];

        for i in _env_wires {
            args.push(downcast_wire(i).0.clone());
        }

        for i in _wrs {
            args.push(downcast_wr(i).index_by_var("i"));
        }

        writeln!(self.current_output().borrow_mut(),"    for i in 0..{} {{",n,).expect("");
        writeln!(self.current_output().borrow_mut(),"        let result = {}(&ctx, {});",fn_name,args.join(", ")).expect("");
        for i in 0..out_wrs.len() {
            writeln!(self.current_output().borrow_mut(),"        {}[{}].push(Var::new(result[{}]));",out_w.0,i,i).expect("");
        }
        writeln!(self.current_output().borrow_mut(),"    }}").expect("");

        upcast_wrs(out_wrs)
    }

    fn get_witness_wr(&self, m: &NatType, n: usize) -> WireRange {
        let wr = self.new_wire_range(m, n);
        writeln!(self.current_output().borrow_mut(),"    let mut {} = Vec::with_capacity({});",wr.name,n).expect("");
        writeln!(self.current_output().borrow_mut(),"    for _ in 0..{} {{",n).expect("");
        writeln!(self.current_output().borrow_mut(),"        let s = ctx.witness();").expect("");
        writeln!(self.current_output().borrow_mut(),"        {}.push(s);",wr.name).expect("");
        writeln!(self.current_output().borrow_mut(),"    }}").expect("");
        upcast_wr(wr)
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

    let f_src = File::create("../../zksc-air/src/main.rs").expect("Should be able to open icicle output file");
    let f_src_writer = Rc::new(RefCell::new(BufWriter::new(f_src)));


    let f_fun = File::create("../../zksc-air/src/funs.rs").expect("Should be able to open icicle function file");
    let f_fun_writer = Rc::new(RefCell::new(BufWriter::new(f_fun)));


    let sieve = Box::new(ZKSCAIRIMPL::new(f_src_writer,f_fun_writer));

    set_boxed_sieve_backend(sieve);
    zksc_run(
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
    )
}
