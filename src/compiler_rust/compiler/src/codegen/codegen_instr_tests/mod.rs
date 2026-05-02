//! Codegen-level tests for MIR instruction compilation.
//!
//! These tests construct MIR directly (bypassing lowering) and compile via AOT
//! (Cranelift ObjectModule) to verify each `compile_instruction` match arm in
//! `instr/mod.rs` produces valid native code. AOT avoids SIGSEGV issues with
//! multiple JIT instances in one process.

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
pub(super) fn build_module(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) -> MirModule {
    let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
    let ret = build(&mut func);
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
    let mut module = MirModule::new();
    module.functions.push(func);
    module
}

/// Compile a MIR module to object code via AOT. Returns true if successful.
pub(super) fn aot_compiles(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) -> bool {
    let module = build_module(name, build);
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen.compile_module(&module).is_ok()
}

/// Compile a MIR module with globals via AOT.
pub(super) fn aot_compiles_module(module: MirModule) -> bool {
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen.compile_module(&module).is_ok()
}

mod constants;
mod memory;
mod coverage_units;
mod enum_union;
mod collections;
mod calls;
mod simd;
mod gpu;
mod inline_asm;
