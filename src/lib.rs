#![warn(missing_debug_implementations, rust_2018_idioms)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(dead_code)] // XXX during development

mod ccs;
mod espresso;

pub use espresso::errors::ArithErrors;
