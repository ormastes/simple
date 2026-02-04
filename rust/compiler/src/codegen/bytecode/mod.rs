//! MIR-to-bytecode compiler.
//!
//! This module compiles MIR functions to bytecode that can be executed
//! by the bytecode VM in `simple-runtime`.

pub mod compiler;

#[cfg(test)]
mod compiler_tests;
