//! LLVM backend tests
//!
//! Tests for LLVM-based code generation supporting 32-bit and 64-bit targets.
//! This backend complements Cranelift by providing broader architecture support.
//!
//! NOTE: Most tests require the `llvm` feature flag to be enabled.
//!
//! ## Test Categories
//!
//! - **backend_creation**: Backend initialization for different architectures (5 tests)
//! - **type_mapping**: Type system and pointer width tests (3 tests)
//! - **compilation**: Basic compilation and backend trait tests (5 tests)
//! - **ir_generation**: LLVM IR generation, modules, and function signatures (6 tests)
//! - **function_compilation**: Complete functions with basic blocks and parameters (3 tests)
//! - **binop**: Binary operations - integer and floating point (4 tests)
//! - **control_flow**: If/else, phi nodes, conditional branches (3 tests)
//! - **object_emission**: ELF object file generation (5 tests)
//! - **mir_compilation**: MIR to LLVM translation (7 tests)
//!
//! Total: 41 tests organized into 9 focused modules

#[cfg(test)]
mod backend_creation;
#[cfg(test)]
mod binop;
#[cfg(test)]
mod compilation;
#[cfg(test)]
mod control_flow;
#[cfg(test)]
mod function_compilation;
#[cfg(test)]
mod ir_generation;
#[cfg(test)]
mod mir_compilation;
#[cfg(test)]
mod object_emission;
#[cfg(test)]
mod type_mapping;
