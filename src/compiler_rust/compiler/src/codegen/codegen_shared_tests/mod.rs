//! Shared codegen emitter tests that run the same MIR instruction sequences
//! through multiple `CodegenEmitter` backends via `dispatch_instruction()`.
//!
//! Currently tests:
//! - **MIR Interpreter** (`MirInterpreterEmitter`): always runs
//! - **Cranelift AOT** (`Codegen::compile_module`): always runs
//! - **LLVM** (`LlvmEmitter`): runs when `llvm` feature is enabled
//!
//! Each test builds MIR instructions and verifies all backends handle them.

use crate::codegen::dispatch::dispatch_instruction;
use crate::codegen::mir_interpreter::MirInterpreterEmitter;
use crate::codegen::Codegen;
use crate::hir::{self, PointerKind, TypeId};
use crate::mir::{
    BlockId, ContractKind, FStringPart, GpuAtomicOp, GpuMemoryScope, LocalKind, MirFunction, MirInst, MirLiteral,
    MirLocal, MirModule, MirPattern, ParallelBackend, PatternBinding, Terminator, UnitOverflowBehavior, VReg,
};
use simple_parser::ast::Visibility;

// =============================================================================
// Backend harness functions
// =============================================================================

/// Run MIR instructions through the interpreter emitter. Returns Ok(()) on success.
fn interpreter_ok(insts: &[MirInst]) {
    let mut emitter = MirInterpreterEmitter::new();
    for inst in insts {
        dispatch_instruction(&mut emitter, inst).unwrap_or_else(|e| panic!("interpreter failed on {:?}: {}", inst, e));
    }
}

/// Run MIR instructions through the interpreter and return the value of a vreg.
fn interpreter_value(insts: &[MirInst], vreg: VReg) -> i64 {
    let mut emitter = MirInterpreterEmitter::new();
    for inst in insts {
        dispatch_instruction(&mut emitter, inst).unwrap_or_else(|e| panic!("interpreter failed on {:?}: {}", inst, e));
    }
    emitter.get(vreg)
}

/// Build a MirModule from instructions and compile via Cranelift AOT.
fn cranelift_ok(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) {
    let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
    let ret = build(&mut func);
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
    let mut module = MirModule::new();
    module.functions.push(func);
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen
        .compile_module(&module)
        .unwrap_or_else(|e| panic!("cranelift compilation failed for {}: {:?}", name, e));
}

/// Compile a pre-built MirModule via Cranelift AOT.
fn cranelift_module_ok(module: MirModule) {
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen
        .compile_module(&module)
        .unwrap_or_else(|e| panic!("cranelift module compilation failed: {:?}", e));
}

// =============================================================================
// Shared test macro
// =============================================================================

/// Generate a cranelift-only test (for ops unsupported by the interpreter).
macro_rules! cranelift_only_test {
    ($name:ident, $build:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn cranelift() {
                cranelift_ok(stringify!($name), $build);
            }
        }
    };
}

/// Generate tests that run the same instruction sequence through all backends.
///
/// Usage:
/// ```ignore
/// shared_test!(test_name, |f| {
///     // build instructions using f: &mut MirFunction
///     // return the VReg to use as return value
///     dest
/// });
/// ```
macro_rules! shared_test {
    ($name:ident, $build:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn cranelift() {
                cranelift_ok(stringify!($name), $build);
            }

            #[test]
            fn interpreter() {
                // Build a function, extract instructions, run through interpreter
                let mut func = MirFunction::new(stringify!($name).to_string(), TypeId::I64, Visibility::Public);
                let _ret = ($build)(&mut func);
                let insts: Vec<MirInst> = func.block_mut(BlockId(0)).unwrap().instructions.clone();
                interpreter_ok(&insts);
            }
        }
    };
}

/// Like shared_test but for tests that need a custom module (multiple functions, globals).
/// Takes a closure that returns a MirModule and a Vec<MirInst> for interpreter testing.
macro_rules! shared_module_test {
    ($name:ident, module: $module_build:expr, insts: $insts_build:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn cranelift() {
                cranelift_module_ok($module_build);
            }

            #[test]
            fn interpreter() {
                let insts = $insts_build;
                interpreter_ok(&insts);
            }
        }
    };
}

// =============================================================================
// Submodules
// =============================================================================

mod basic_tests;
mod collection_tests;
mod memory_tests;
mod vector_tests;
mod interpreter_tests;
mod binop_extra_tests;
mod pointer_unit_tests;
mod string_method_tests;
mod builtin_method_tests;
mod call_coverage_tests;
mod control_flow_tests;
