//! Memory, struct, field, pointer, and lvalue method call tests for MIR lowering

use super::super::common::*;
use super::helpers::*;
use crate::hir::{self, HirExpr, HirExprKind};
use crate::mir::lower::MirLowerer;
use crate::mir::function::MirFunction;
use crate::mir::{CallTarget, MirInst};

// --- lvalue MethodCall branch (property access on struct) ---

#[test]
fn lvalue_method_call_with_struct_registry() {
    let mut lowerer = gpu_lowerer_setup();
    let mut registry = hir::TypeRegistry::new();
    let struct_ty = registry.register(hir::HirType::Struct {
        name: "Point".to_string(),
        fields: vec![("x".to_string(), hir::TypeId::I64), ("y".to_string(), hir::TypeId::I64)],
        has_snapshot: false,
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: std::collections::HashMap::new(),
    });
    // We need to set the type_registry on lowerer WHILE function is active
    // This is tricky because type_registry is a reference.
    // Use a leaked reference for test purposes.
    let registry_ref: &'static hir::TypeRegistry = Box::leak(Box::new(registry));
    lowerer.type_registry = Some(registry_ref);

    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Local(0),
        ty: struct_ty,
    });
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "x".to_string(),
            args: vec![],
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GetElementPtr { .. })));
}

#[test]
fn lvalue_method_call_no_registry_fallback() {
    let mut lowerer = gpu_lowerer_setup();
    // No type_registry set -> falls through to runtime setter path
    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Integer(0),
        ty: hir::TypeId::I64,
    });
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "x".to_string(),
            args: vec![],
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok()); // Falls back to returning receiver register
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_method_call_non_struct_type() {
    let mut lowerer = gpu_lowerer_setup();
    let mut registry = hir::TypeRegistry::new();
    // Register an enum, not a struct — so the Struct match fails
    let enum_ty = registry.register(hir::HirType::Enum {
        name: "Color".to_string(),
        variants: vec![("Red".to_string(), None)],
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: std::collections::HashMap::new(),
    });
    let registry_ref: &'static hir::TypeRegistry = Box::leak(Box::new(registry));
    lowerer.type_registry = Some(registry_ref);

    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Local(0),
        ty: enum_ty,
    });
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "x".to_string(),
            args: vec![],
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok()); // Falls through to runtime setter
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_method_call_field_not_found() {
    let mut lowerer = gpu_lowerer_setup();
    let mut registry = hir::TypeRegistry::new();
    let struct_ty = registry.register(hir::HirType::Struct {
        name: "Point".to_string(),
        fields: vec![("x".to_string(), hir::TypeId::I64)],
        has_snapshot: false,
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: std::collections::HashMap::new(),
    });
    let registry_ref: &'static hir::TypeRegistry = Box::leak(Box::new(registry));
    lowerer.type_registry = Some(registry_ref);

    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Local(0),
        ty: struct_ty,
    });
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "z".to_string(), // field doesn't exist
            args: vec![],
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok()); // Falls through to runtime setter
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_method_call_no_registry_method_with_args() {
    // MethodCall with args -> doesn't match the args.is_empty() guard -> falls to catch-all
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Integer(0),
        ty: hir::TypeId::I64,
    });
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "foo".to_string(),
            args: vec![gpu_dummy_expr()], // non-empty args
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err()); // Falls to catch-all unsupported
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_method_call_receiver_fails() {
    // MethodCall with struct field found but receiver lower_lvalue fails
    let mut lowerer = gpu_lowerer_setup();
    let mut registry = hir::TypeRegistry::new();
    let struct_ty = registry.register(hir::HirType::Struct {
        name: "Pt".to_string(),
        fields: vec![("x".to_string(), hir::TypeId::I64)],
        has_snapshot: false,
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: std::collections::HashMap::new(),
    });
    let registry_ref: &'static hir::TypeRegistry = Box::leak(Box::new(registry));
    lowerer.type_registry = Some(registry_ref);

    // Receiver is Integer(0) which fails in lower_lvalue
    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Integer(0),
        ty: struct_ty,
    });
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "x".to_string(),
            args: vec![],
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_method_call_receiver_expr_fails() {
    // MethodCall where field not found, so it falls to runtime setter path
    // but receiver lower_expr fails
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(failing_expr());
    let expr = HirExpr {
        kind: HirExprKind::MethodCall {
            receiver,
            method: "x".to_string(),
            args: vec![],
            dispatch: crate::hir::DispatchMode::Dynamic,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}
