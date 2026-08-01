//! Branch coverage tests for MIR lowering
//!
//! These tests exercise specific code paths in lowering_expr.rs, lowering_stmt.rs,
//! lowering_core.rs, and lowering_types.rs that are not covered by basic_lowering tests.
//! They compile Simple source to MIR and inspect the generated instructions without
//! executing through JIT.
//!
//! Split into submodules for maintainability:

mod helpers;
mod expr;
mod types;
mod control;
mod calls;
mod gpu;
mod gpu_errors;
mod memory;
mod misc;
mod misc_coverage;
mod direct;
