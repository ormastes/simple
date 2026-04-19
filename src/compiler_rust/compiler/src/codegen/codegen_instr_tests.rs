//! Codegen-level tests for MIR instruction compilation.
//!
//! These tests construct MIR directly (bypassing lowering) and compile via AOT
//! (Cranelift ObjectModule) to verify each `compile_instruction` match arm in
//! `instr/mod.rs` produces valid native code. AOT avoids SIGSEGV issues with
//! multiple JIT instances in one process.
//!
//! Tests are split by instruction category:
//! - `scalar`      — constants, basic ops, binop, cast
//! - `memory`      — memory, boxing, drop, coverage, units, enums, unions, result, pointers, contracts, spread
//! - `aggregates`  — collections, strings, structs, closures, methods, patterns, interpreter, globals
//! - `concurrent`  — async, generators, actors, parallel iterators
//! - `gpu`         — GPU/SIMD, atomic, intrinsics, actors, call

use crate::codegen::Codegen;
use crate::hir::{self, PointerKind, TypeId};
use crate::mir::{MirFunction, MirLocal, MirModule, LocalKind};
use crate::mir::{
    BlockId, ContractKind, FStringPart, GpuAtomicOp, GpuMemoryScope, MirInst, MirLiteral, MirPattern, ParallelBackend,
    PatternBinding, Terminator, UnitOverflowBehavior, VReg,
};
use simple_parser::ast::Visibility;

/// Build a MirModule with a single function that:
/// - Has no parameters
/// - Returns i64
/// - Executes the given instructions, then returns `ret_vreg`
fn build_module(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) -> MirModule {
    let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
    let ret = build(&mut func);
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
    let mut module = MirModule::new();
    module.functions.push(func);
    module
}

/// Compile a MIR module to object code via AOT. Returns true if successful.
fn aot_compiles(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) -> bool {
    let module = build_module(name, build);
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen.compile_module(&module).is_ok()
}

/// Compile a MIR module with globals via AOT.
fn aot_compiles_module(module: MirModule) -> bool {
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen.compile_module(&module).is_ok()
}

#[path = "codegen_instr_tests_scalar.rs"]
mod scalar;

#[path = "codegen_instr_tests_memory.rs"]
mod memory;

#[path = "codegen_instr_tests_aggregates.rs"]
mod aggregates;

#[path = "codegen_instr_tests_concurrent.rs"]
mod concurrent;

#[path = "codegen_instr_tests_gpu.rs"]
mod gpu;
