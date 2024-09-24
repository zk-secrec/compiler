/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use std::{env, error::Error, fs, rc::Rc};

use crate::ResourceLoader;

pub fn fs_circuit_loader(dir: &str) -> ResourceLoader<str> {
    let root_path = String::from(dir);
    let load_circuit = move |circuit_name: String| -> Option<Rc<str>> {
        let path = format!("{root_path}/{circuit_name}.txt");
        match fs::read_to_string(path) {
            Ok(contents) => Some(Rc::from(contents)),
            Err(_) => None,
        }
    };

    Box::new(load_circuit)
}

fn try_read_to_string<S: AsRef<str>>(path: S) -> Option<String> {
    if path.as_ref() == "" {
        None
    } else {
        Some(fs::read_to_string(path.as_ref()).expect(""))
    }
}

pub struct CommandLineArgs {
    pub input_public: Option<String>,
    pub input_instance: Option<String>,
    pub input_witness: Option<String>,
    pub circuit_loader: ResourceLoader<str>,
    pub output_prefix: String,
}

pub fn parse_command_line_args() -> Result<CommandLineArgs, Box<dyn Error>> {
    let args = &env::args().collect::<Vec<_>>();
    if args.len() < 4 {
        Err(String::from(
            "Too few command line arguments. Usage: {args[0]} public_json instance_json witness_json\""
        ))?
    }

    let circuit_directory = if args.len() > 4 { &args[4] } else { "" };
    let circuit_loader = fs_circuit_loader(circuit_directory);
    let output_prefix = String::from(if args.len() > 5 { &args[5] } else { "" });
    let input_public = try_read_to_string(&args[1]);
    let input_instance = try_read_to_string(&args[2]);
    let input_witness = try_read_to_string(&args[3]);
    Ok(CommandLineArgs {
        input_public,
        input_instance,
        input_witness,
        circuit_loader,
        output_prefix,
    })
}
