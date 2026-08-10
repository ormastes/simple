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
        .any(pred)
}

/// Helper: count instructions matching a predicate
pub(super) fn count_inst(mir: &MirModule, pred: impl Fn(&MirInst) -> bool) -> usize {
    mir.functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .filter(|inst| pred(inst))
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
    lowerer.type_registry = Some(failing_expr_registry());
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

/// Helper: make an expression that causes lower_expr to return Err.
///
/// `Bogus` is a REGISTERED enum (see `failing_expr_registry`) that positively
/// does not declare `Nope`, which is what makes `lower_global_expr` reject it.
/// An unregistered head is deliberately NOT enough: unresolved heads stay
/// permissive so cross-module type-registry metadata loss cannot fail a build.
pub(super) fn failing_expr() -> HirExpr {
    HirExpr {
        kind: HirExprKind::Global("Bogus::Nope".to_string()),
        ty: hir::TypeId::I64,
    }
}

/// A leaked registry declaring `enum Bogus { Real }` so `failing_expr()` resolves
/// its head positively and its tail negatively.
pub(super) fn failing_expr_registry() -> &'static hir::TypeRegistry {
    use std::sync::OnceLock;
    static REGISTRY: OnceLock<&'static hir::TypeRegistry> = OnceLock::new();
    REGISTRY.get_or_init(|| {
        let mut registry = hir::TypeRegistry::new();
        registry.register_named(
            "Bogus".to_string(),
            hir::HirType::Enum {
                name: "Bogus".to_string(),
                variants: vec![("Real".to_string(), None)],
                generic_params: vec![],
                is_generic_template: false,
                type_bindings: Default::default(),
            },
        );
        Box::leak(Box::new(registry))
    })
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
    func.blocks.iter().flat_map(|b| b.instructions.iter()).any(pred)
}
