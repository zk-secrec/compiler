pub mod symbolic;
pub mod air_gen;
pub mod function_scope;
pub mod funs;

pub use symbolic::{Var, Op, SymbolicContext};
pub use air_gen::{DynamicAIR, extract_and_print_constraints, generate_and_print_trace};
pub use function_scope::{FunctionScope, ScopedContext};
