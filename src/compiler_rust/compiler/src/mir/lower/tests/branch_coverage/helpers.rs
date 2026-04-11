//! Shared helpers for branch_coverage test submodules

use super::super::common::*;
use crate::hir::{self, GpuIntrinsicKind, HirExpr, HirExprKind};
use crate::mir::lower::{lower_to_mir_with_coverage, MirLowerResult, MirLowerer};
use crate::mir::function::{MirFunction, MirModule};
use crate::mir::{CallTarget, MirInst};
use simple_parser::Parser;

/// Helper: compile with coverage enabled
pub(super) fn compile_with_coverage(source: &str) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir_with_coverage(&hir_module, true)
}

/// Helper: check if any instruction in the module matches a predicate
pub(super) fn has_inst(mir: &MirModule, pred: impl Fn(&MirInst) -> bool) -> bool {
    mir.functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .any(|i| pred(i))
}

/// Helper: count instructions matching a predicate
pub(super) fn count_inst(mir: &MirModule, pred: impl Fn(&MirInst) -> bool) -> usize {
    mir.functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .filter(|i| pred(i))
        .count()
}

/// Helper: make an integer HirExpr for GPU args
pub(super) fn gpu_int_expr(val: i64) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Integer(val),
        ty: hir::TypeId::I64,
    }
}

/// Helper: make a dummy HirExpr (local var) for GPU args that need lowered exprs
pub(super) fn gpu_dummy_expr() -> HirExpr {
    HirExpr {
        kind: HirExprKind::Integer(0),
        ty: hir::TypeId::I64,
    }
}

/// Helper: set up MirLowerer for GPU tests
pub(super) fn gpu_lowerer_setup() -> MirLowerer<'static> {
    let mut lowerer = MirLowerer::new();
    let mut func = MirFunction::new(
        "gpu_test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "gpu_test", false).unwrap();
    lowerer
}

pub(super) fn gpu_result_is_materialized_nil(func: &MirFunction, result: crate::mir::instructions::VReg) -> bool {
    func.blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::ConstInt { dest, value } if *dest == result && *value == 3))
}

/// Helper: make an expression that causes lower_expr to return Err
/// (unknown enum variant with no registry)
pub(super) fn failing_expr() -> HirExpr {
    HirExpr {
        kind: HirExprKind::Global("Bogus::Nope".to_string()),
        ty: hir::TypeId::I64,
    }
}

/// Helper: build a MirFunction with one block, push instructions, return it.
pub(super) fn build_mir_func(name: &str, build: impl FnOnce(&mut MirFunction)) -> MirFunction {
    let mut func = MirFunction::new(
        name.to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    build(&mut func);
    func
}

/// Helper: check if any instruction in a function matches a predicate.
pub(super) fn func_has_inst(func: &MirFunction, pred: impl Fn(&MirInst) -> bool) -> bool {
    func.blocks.iter().flat_map(|b| b.instructions.iter()).any(|i| pred(i))
}
