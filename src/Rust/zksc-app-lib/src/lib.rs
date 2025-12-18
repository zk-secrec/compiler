/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

pub mod value;
pub mod value_conversions;
pub mod context;
pub mod integer;
pub mod zksc_types;
pub mod consts;
pub mod sieve;
#[cfg(feature = "oob_challenge")]
pub mod oob_challenge;
#[cfg(feature = "command_line")]
pub mod command_line;
#[macro_use]
pub mod zksc_integer;

pub use value::*;
pub use value_conversions::*;
pub use context::*;
pub use integer::*;
pub use sieve::*;
pub use zksc_types::*;
pub use consts::*;
#[cfg(feature = "command_line")]
pub use command_line::*;

mod stack;
mod circuit_parser;
mod builtins;
#[macro_use]
mod generated;
mod call_circom;
mod externs;
mod externs_header;
mod externs_stdlib;

pub fn zksc_run(
    input_public: Option<&str>,
    input_instance: Option<&str>,
    input_witness: Option<&str>,
    circuit_content_loader: ResourceLoader<str>) -> Result<()>
{
    generated::run(
        input_public,
        input_instance,
        input_witness,
        circuit_content_loader)
}
