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
    io::{BufRead, BufReader, BufWriter, Stdout, Write},
    net::{TcpListener, TcpStream},
    rc::Rc,
};

use num_bigint::RandBigInt;
use num_traits::{Zero, One, ToPrimitive};

use crate::{consts::*, integer::*, sieve::*, zksc_types::*, Value, rep};

pub struct OobChallengeBackend {
    integer_zero: Integer,
    output: Rc<RefCell<BufWriter<Stdout>>>,
    challenges_read: Option<RefCell<BufReader<TcpStream>>>,
    challenges_write: Option<RefCell<BufWriter<TcpStream>>>,
    emp_read: Option<RefCell<std::fs::File>>,
}

//#[macro_export]
macro_rules! write_output {
    ($ctx:ident $(,$x:expr)*) => {
        writeln!($ctx.output.borrow_mut() $(,$x)*).expect("Failed to write output");
    };
}

impl OobChallengeBackend {
    pub fn new(output: Rc<RefCell<BufWriter<Stdout>>>, output_prefix: &str) -> Self {
        output.borrow_mut().flush().expect("");
        let (challenges_read, challenges_write, emp_read) = if INTERACTIVE {
            let addr = CHALLENGE_TCP;
            match CURR_DOMAIN {
                Public => (None, None, None),
                Verifier => {
                    writeln!(output.borrow_mut(), "Connecting to {}", addr).expect("");
                    output.borrow_mut().flush().expect("");
                    let stream = TcpStream::connect(addr).expect("Could not connect");
                    let emp = std::fs::File::open(output_prefix.to_owned() + ".emp")
                        .expect("Failed to open .emp file for reading");
                    (
                        None,
                        Some(RefCell::new(BufWriter::new(stream))),
                        Some(RefCell::new(emp)),
                    )
                }
                Prover => {
                    let listener = TcpListener::bind(addr)
                        .expect(&format!("Failed to bind to the address {}", addr));
                    writeln!(output.borrow_mut(), "Listening to {}", addr).expect("");
                    output.borrow_mut().flush().expect("");
                    let (stream, _) = listener.accept().expect("Could not connect");
                    (Some(RefCell::new(BufReader::new(stream))), None, None)
                }
            }
        } else {
            (None, None, None)
        };

        OobChallengeBackend {
            integer_zero: Integer::zero(),
            output: output.clone(),
            challenges_read,
            challenges_write,
            emp_read,
        }
    }

    fn gen_challenge(&self, m: &Integer) -> Integer {
        rand::thread_rng().gen_bigint_range(&self.integer_zero, m)
    }

    fn challenge1(&self, sieve: &dyn SIEVEIR, m: &NatType) -> Value {
        let mut m_bi = match m.modulus {
            Some(ref m) => m,
            _ => panic!("Infinite modulus not supported in $post"),
        };
        let m_bitwise;
        if m.ring_type == RingBitwise {
            // for bitwise rings, m.modulus contains the number of bits, not the modulus
            m_bitwise = Integer::one() << m_bi.to_usize().unwrap();
            m_bi = &m_bitwise;
        }
        match CURR_DOMAIN {
            Public => panic!("Not expecting public domain"),
            Verifier => {
                let r = self.gen_challenge(m_bi);
                write_output!(self, "Challenge = {}", r);
                if INTERACTIVE {
                    sieve.flush();
                    let mut s = self.challenges_write.as_ref().unwrap().borrow_mut();
                    writeln!(s, "{}", r).expect("");
                    s.flush().expect("");
                }

                (m.from_bigint)(&r)
            }
            Prover => {
                let r = if INTERACTIVE {
                    sieve.flush();
                    let mut line = String::new();
                    self.challenges_read
                        .as_ref()
                        .unwrap()
                        .borrow_mut()
                        .read_line(&mut line)
                        .expect("Failed to read challenge");
                    int_lit(line.trim())
                } else {
                    self.gen_challenge(m_bi)
                };
                write_output!(self, "Challenge: {}", r);
                (m.from_bigint)(&r)
            }
        }
    }
}

fn read_line_unbuffered(f: &mut std::fs::File) {
    use std::io::Read;
    let mut buffer = [0; 1];
    loop {
        f.read(&mut buffer).expect("");
        if buffer[0] == 10 {
            break;
        }
    }
}

impl ChallengeBackend for OobChallengeBackend {
    fn challenge(&self, sieve: &dyn SIEVEIR, m: &NatType, n: usize) -> Value {
        let mut res: Vec<Value> = Vec::new();
        for _ in 0 .. n {
            res.push(self.challenge1(sieve, m));
        }
        rep::Array::new(res)
    }

    fn read_emp_line_1(&self) {
        if INTERACTIVE && CURR_DOMAIN == Verifier {
            read_line_unbuffered(&mut self.emp_read.as_ref().unwrap().borrow_mut());
        }
    }

    fn read_witness_confirmation(&self, ctx: &dyn SIEVEIR) {
        if INTERACTIVE {
            ctx.flush();
        }
        if INTERACTIVE && CURR_DOMAIN == Verifier {
            read_line_unbuffered(&mut self.emp_read.as_ref().unwrap().borrow_mut());
        }
    }
}
