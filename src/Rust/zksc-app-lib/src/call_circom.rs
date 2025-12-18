use crate::externs_header::*;
use crate::builtins::{get_or_create_wire, get_pre_or_post_uint, SoA};
use crate::rep;
use crate::{sieve_backend, Wire, Constraint, LinearCombination, CURR_DOMAIN, DomainType::Prover};

use std::fs;
use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};
use std::process::Command;
use num_bigint;
use num_bigint::Sign;

struct Section {
    s_type: u32,
    s_data: Vec<u8>,
}

struct SectionList {
    magic: u32,
    #[allow(unused)]
    version: u32,
    sections: Vec<Section>,
}

impl SectionList {
    fn get_section<'a>(&'a self, s_type: u32) -> &'a Section {
        for s in &self.sections {
            if s.s_type == s_type {
                return s; 
            }
        }
        panic!("section not found")
    }
}

struct R1CSHeader {
    field_num_bytes: usize,
    prime: BigInt,
    num_wires: usize,
    num_public_outputs: usize,
    num_public_inputs: usize,
    num_private_inputs: usize,
    num_constraints: usize,
}

struct WtnsHeader {
    field_num_bytes: usize,
    prime: BigInt,
    num_wires: usize,
}

fn translate_linear_combination(wires: &Vec<Option<Wire>>, lc: LinearCombination<usize>) -> LinearCombination<Option<Wire>> {
    lc.into_iter().map(|(w, c)| (wires[w].clone(), c)).collect()
}

fn translate_constraint(wires: &Vec<Option<Wire>>, c: Constraint<usize>) -> Constraint<Option<Wire>> {
    Constraint {
        a: translate_linear_combination(wires, c.a),
        b: translate_linear_combination(wires, c.b),
        c: translate_linear_combination(wires, c.c),
    }
}

fn parse_r1cs_header(s: &Section) -> R1CSHeader {
    let data = &s.s_data;
    let field_num_bytes = u32::from_le_bytes(data[0..4].try_into().unwrap()) as usize;
    let prime = BigInt::from_bytes_le(Sign::Plus, &data[4 .. 4 + field_num_bytes]);
    //println!("field_num_bytes: {}", field_num_bytes);
    //println!("prime: {}", prime);
    let mut offset = 4 + field_num_bytes;
    let num_wires = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap()) as usize;
    offset += 4;
    let num_public_outputs = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap()) as usize;
    offset += 4;
    let num_public_inputs = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap()) as usize;
    offset += 4;
    let num_private_inputs = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap()) as usize;
    offset += 4;
    // skip num_labels
    offset += 8;
    let num_constraints = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap()) as usize;
    //println!("num_wires: {}", num_wires);
    //println!("num_public_outputs: {}", num_public_outputs);
    //println!("num_public_inputs: {}", num_public_inputs);
    //println!("num_private_inputs: {}", num_private_inputs);
    //println!("num_constraints: {}", num_constraints);
    R1CSHeader { field_num_bytes, prime, num_wires, num_public_outputs, num_public_inputs, num_private_inputs, num_constraints }
}

fn parse_wtns_header(s: &Section) -> WtnsHeader {
    let data = &s.s_data;
    let field_num_bytes = u32::from_le_bytes(data[0..4].try_into().unwrap()) as usize;
    let prime = BigInt::from_bytes_le(Sign::Plus, &data[4 .. 4 + field_num_bytes]);
    //println!("field_num_bytes: {}", field_num_bytes);
    //println!("prime: {}", prime);
    let offset = 4 + field_num_bytes;
    let num_wires = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap()) as usize;
    //println!("num_wires: {}", num_wires);
    WtnsHeader { field_num_bytes, prime, num_wires }
}

fn parse_linear_combination(h: &R1CSHeader, offset: &mut usize, data: &Vec<u8>) -> LinearCombination<usize> {
    let n = u32::from_le_bytes(data[*offset .. *offset + 4].try_into().unwrap()) as usize;
    *offset += 4;
    let mut lc = Vec::new();
    for _ in 0 .. n {
        let w = u32::from_le_bytes(data[*offset .. *offset + 4].try_into().unwrap()) as usize;
        *offset += 4;
        let c = BigInt::from_bytes_le(Sign::Plus, &data[*offset .. *offset + h.field_num_bytes]);
        *offset += h.field_num_bytes;
        lc.push((w, c));
    }
    lc
}

fn parse_constraints(h: &R1CSHeader, s: &Section) -> Vec<Constraint<usize>> {
    let mut constraints = Vec::new();
    let mut offset = 0;
    let data = &s.s_data;
    for _ in 0 .. h.num_constraints {
        let a = parse_linear_combination(h, &mut offset, data);
        let b = parse_linear_combination(h, &mut offset, data);
        let c = parse_linear_combination(h, &mut offset, data);
        constraints.push(Constraint { a, b, c });
    }
    constraints
}

fn parse_witness_values(h: &WtnsHeader, s: &Section) -> Vec<BigInt> {
    let data = &s.s_data;
    let mut offset = 0;
    let mut res = Vec::new();
    for _i in 0 .. h.num_wires {
        let x = BigInt::from_bytes_le(Sign::Plus, &data[offset .. offset + h.field_num_bytes]);
        offset += h.field_num_bytes;
        //println!("value[{}]: {}", _i, x);
        res.push(x);
    }
    res
}

fn extract_sections(data: Vec<u8>) -> SectionList {
    let magic = u32::from_le_bytes(data[0..4].try_into().unwrap());
    let version = u32::from_le_bytes(data[4..8].try_into().unwrap());
    //println!("version {}", version);
    let num_sections = u32::from_le_bytes(data[8..12].try_into().unwrap());
    //println!("number of sections: {}", num_sections);
    let mut sections = Vec::new();
    let mut offset = 12;
    for _ in 0 .. num_sections {
        let s_type = u32::from_le_bytes(data[offset .. offset + 4].try_into().unwrap());
        let s_size = u64::from_le_bytes(data[offset + 4 .. offset + 12].try_into().unwrap()) as usize;
        //println!("section type: {}, size {}", s_type, s_size);
        offset += 12;
        let s_data = data[offset .. offset + s_size].to_vec();
        sections.push(Section { s_type, s_data });
        offset += s_size;
    }

    SectionList {
        magic,
        version,
        sections,
    }
}

const DIR: &str = "../../circom-frontend";

#[allow(unused)]
pub fn call_circom(ctx: &ContextRef, _: &mut Stack, modulus: &NatType, name: &String, ins: &Vec<Value>, wit: &Vec<Value>) -> Value {
    //println!("call_circom");
    let data: Vec<u8> = fs::read(format!("{}/{}.r1cs", DIR, name)).expect(&format!("Circuit file {}.r1cs not found", name));
    //println!("Parsing the r1cs file");
    let sl = extract_sections(data);
    assert_eq!(sl.magic, 0x73633172, "The file is not in r1cs file format");
    let header = parse_r1cs_header(sl.get_section(1));
    let constraints = parse_constraints(&header, sl.get_section(2));
    assert_eq!(header.num_public_inputs, ins.len(), "Number of instance values given to call_circom differs from that expected by the circuit");
    assert_eq!(header.num_private_inputs, wit.len(), "Number of witness values given to call_circom differs from that expected by the circuit");
    assert_eq!(&header.prime, modulus.modulus.as_ref().unwrap(), "call_circom called with a different modulus than that expected by the circuit");
    //assert_eq!(header.num_public_outputs, 0, "Circom circuits with verifier's outputs not (yet) supported");
    let num_extra_wit = header.num_wires - 1 - header.num_public_outputs - header.num_public_inputs - header.num_private_inputs;
    let mut output_values = Vec::new();
    if CURR_DOMAIN == Prover && (num_extra_wit > 0 || header.num_public_outputs > 0) {
        let mut f = BufWriter::new(File::create(format!("{}/{}_prover_input.json", DIR, name)).expect("Failed to open file for writing"));
        writeln!(f, "{{").unwrap();
        writeln!(f, "\"wit\":").unwrap();
        writeln!(f, "[").unwrap();
        let mut b = false;
        for x in wit {
            writeln!(f, "{}\"{}\"", if b {","} else {""}, get_pre_or_post_uint(modulus, x)).unwrap();
            b = true;
        }
        writeln!(f, "],").unwrap();
        writeln!(f, "\"ins\":").unwrap();
        writeln!(f, "[").unwrap();
        b = false;
        for x in ins {
            writeln!(f, "{}\"{}\"", if b {","} else {""}, get_pre_or_post_uint(modulus, x)).unwrap();
            b = true;
        }
        writeln!(f, "]").unwrap();
        writeln!(f, "}}").unwrap();
        f.flush().unwrap();
        drop(f);
        //println!("Calling the witness extender");
        let output = Command::new("./extend_witness").arg(name).current_dir(DIR).output().expect("Call failed");
        if !output.status.success() {
            println!("Witness extender failed:");
            println!("stdout:");
            io::stdout().write_all(&output.stdout).unwrap();
            println!("stderr:");
            io::stdout().write_all(&output.stderr).unwrap();
            panic!("Witness extender failed");
        }
        //println!("Call finished, parsing the wtns file");

        let data: Vec<u8> = fs::read(format!("{}/{}.wtns", DIR, name)).expect(&format!("Witness file {}.wtns not found", name));
        let sl = extract_sections(data);
        assert_eq!(sl.magic, 'w' as u32 + (('t' as u32) << 8) + (('n' as u32) << 16) + (('s' as u32) << 24), "The file is not in wtns file format");
        let wtns_header = parse_wtns_header(sl.get_section(1));
        assert_eq!(header.num_wires, wtns_header.num_wires, "wtns file does not correspond to the same circuit as the r1cs file");
        assert_eq!(header.field_num_bytes, wtns_header.field_num_bytes, "wtns file does not correspond to the same circuit as the r1cs file");
        assert_eq!(header.prime, wtns_header.prime, "wtns file does not correspond to the same circuit as the r1cs file");
        let witness_values = parse_witness_values(&wtns_header, sl.get_section(2));
        for x in &witness_values[1 .. header.num_public_outputs + 1] {
            let v = (modulus.from_bigint)(x);
            sieve_backend().add_witness(modulus, &v);
            output_values.push(v);
        }
        for x in &witness_values[witness_values.len() - num_extra_wit ..] {
            sieve_backend().add_witness(modulus, &(modulus.from_bigint)(x));
        }
    } else {
        for _ in 0 .. header.num_public_outputs {
            // public outputs are treated as prover's outputs here, i.e. the are not declassified and thus unknown to the verifier
            output_values.push(ctx.unknown.clone());
            sieve_backend().add_witness(modulus, &ctx.unknown);
        }
        for _ in 0 .. num_extra_wit {
            sieve_backend().add_witness(modulus, &ctx.unknown);
        }
    }
    let output_wr = sieve_backend().get_witness_wr(modulus, header.num_public_outputs);
    let extra_wit = sieve_backend().get_witness_wr(modulus, num_extra_wit);
    let mut wires = Vec::new();
    wires.push(None); // None corresponds to the constant 1
    for i in 0 .. output_wr.length() {
        wires.push(Some(output_wr.index(i)));
    }
    for x in ins {
        wires.push(Some(get_or_create_wire(modulus, x)));
    }
    for x in wit {
        wires.push(Some(get_or_create_wire(modulus, x)));
    }
    for i in 0 .. extra_wit.length() {
        wires.push(Some(extra_wit.index(i)));
    }
    let constraints: Vec<_> = constraints.into_iter().map(|c| translate_constraint(&wires, c)).collect();
    constraints.iter().for_each(|c| sieve_backend().assert_r1cs_constraint(modulus, c));
    let out = rep::PostSoA::new(SoA::Scalar((output_wr, output_values)));
    out
}
