//! Module boundary checking tests (CTR-012)

use crate::hir::{HirExpr, HirExprKind, HirType, TypeId, TypeRegistry, BinOp};

#[test]
fn test_module_boundary_parameter_invariant() {
    // Test that public functions get preconditions for typed parameters
    // Create an expression: self.x > 0 (local 0 is self, field 0 is x)
    let invariant_expr = HirExpr {
        kind: HirExprKind::Binary {
            op: BinOp::Gt,
            left: Box::new(HirExpr {
                kind: HirExprKind::FieldAccess {
                    receiver: Box::new(HirExpr {
                        kind: HirExprKind::Local(0), // self
                        ty: TypeId::I64,
                    }),
                    field_index: 0,
                },
                ty: TypeId::I64,
            }),
            right: Box::new(HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }),
        },
        ty: TypeId::BOOL,
    };

    // Substitute self (local 0) with parameter at index 2
    let substituted = invariant_expr.substitute_local(0, 2);

    // Verify the substitution
    match &substituted.kind {
        HirExprKind::Binary { left, .. } => match &left.kind {
            HirExprKind::FieldAccess { receiver, .. } => match &receiver.kind {
                HirExprKind::Local(idx) => {
                    assert_eq!(*idx, 2, "Local 0 should be substituted with 2");
                }
                _ => panic!("Expected Local after substitution"),
            },
            _ => panic!("Expected FieldAccess"),
        },
        _ => panic!("Expected Binary"),
    }
}

#[test]
fn test_module_boundary_return_invariant() {
    // Test that public functions get postconditions for typed return values
    // Create an expression: self.valid == true (local 0 is self)
    let invariant_expr = HirExpr {
        kind: HirExprKind::Binary {
            op: BinOp::Eq,
            left: Box::new(HirExpr {
                kind: HirExprKind::FieldAccess {
                    receiver: Box::new(HirExpr {
                        kind: HirExprKind::Local(0), // self
                        ty: TypeId::BOOL,
                    }),
                    field_index: 0,
                },
                ty: TypeId::BOOL,
            }),
            right: Box::new(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
        },
        ty: TypeId::BOOL,
    };

    // Substitute self (local 0) with ContractResult
    let substituted = invariant_expr.substitute_self_with_result();

    // Verify the substitution
    match &substituted.kind {
        HirExprKind::Binary { left, .. } => {
            match &left.kind {
                HirExprKind::FieldAccess { receiver, .. } => {
                    match &receiver.kind {
                        HirExprKind::ContractResult => {
                            // Success - local 0 was substituted with ContractResult
                        }
                        _ => panic!("Expected ContractResult after substitution, got {:?}", receiver.kind),
                    }
                }
                _ => panic!("Expected FieldAccess"),
            }
        }
        _ => panic!("Expected Binary"),
    }
}

#[test]
fn test_get_type_name() {
    // Test TypeRegistry::get_type_name helper for CTR-012
    let mut registry = TypeRegistry::new();

    // Register a struct
    let struct_id = registry.register_named(
        "MyStruct".to_string(),
        HirType::Struct {
            name: "MyStruct".to_string(),
            fields: vec![("x".to_string(), TypeId::I64)],
            has_snapshot: false,
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: std::collections::HashMap::new(),
        },
    );

    // Register an enum
    let enum_id = registry.register_named(
        "MyEnum".to_string(),
        HirType::Enum {
            name: "MyEnum".to_string(),
            variants: vec![("A".to_string(), None), ("B".to_string(), None)],
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: std::collections::HashMap::new(),
        },
    );

    // Test get_type_name
    assert_eq!(registry.get_type_name(struct_id), Some("MyStruct"));
    assert_eq!(registry.get_type_name(enum_id), Some("MyEnum"));
    assert_eq!(registry.get_type_name(TypeId::I64), None); // Primitives don't have names
    assert_eq!(registry.get_type_name(TypeId::STRING), None);
}
