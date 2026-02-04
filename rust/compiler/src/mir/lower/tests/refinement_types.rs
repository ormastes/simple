//! Refinement type tests (CTR-020 to CTR-023)

use crate::hir::{self, BinOp, HirExpr, HirExprKind, HirRefinedType, HirModule, SubtypeResult, TypeId};
use simple_parser::Parser;

#[test]
fn test_refinement_type_parsing() {
    // Test that refined types are properly parsed and stored
    let source = r#"
type PosI64 = i64 where self > 0

fn use_pos(x: PosI64) -> i64:
    return x
"#;
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");

    // Verify the refined type is registered
    assert!(
        hir_module.refined_types.contains_key("PosI64"),
        "Refined type PosI64 should be registered"
    );

    let refined = hir_module.refined_types.get("PosI64").unwrap();
    assert_eq!(refined.name, "PosI64");
    assert_eq!(refined.base_type, crate::hir::TypeId::I64);
}

#[test]
fn test_simple_type_alias_no_predicate() {
    // Test that simple type aliases (without where) work correctly
    let source = r#"
type UserId = i64

fn get_user(id: UserId) -> i64:
    return id
"#;
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");

    // Simple alias should NOT be in refined_types
    assert!(
        !hir_module.refined_types.contains_key("UserId"),
        "Simple type alias should not be in refined_types"
    );

    // But the type name should still be registered
    assert!(
        hir_module.types.lookup("UserId").is_some(),
        "Type alias name should be registered"
    );
}

#[test]
fn test_refined_type_const_eval_greater_than() {
    // CTR-022: Test compile-time evaluation of predicates
    // Create a refined type: PosI64 = i64 where self > 0
    let refined = HirRefinedType {
        name: "PosI64".to_string(),
        base_type: TypeId::I64,
        predicate: HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Gt,
                left: Box::new(HirExpr {
                    kind: HirExprKind::Local(0), // self
                    ty: TypeId::I64,
                }),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Integer(0),
                    ty: TypeId::I64,
                }),
            },
            ty: TypeId::BOOL,
        },
    };

    // Test with positive constant (should satisfy)
    let positive_value = HirExpr {
        kind: HirExprKind::Integer(42),
        ty: TypeId::I64,
    };
    assert_eq!(refined.try_const_eval(&positive_value), Some(true));

    // Test with zero (should NOT satisfy > 0)
    let zero_value = HirExpr {
        kind: HirExprKind::Integer(0),
        ty: TypeId::I64,
    };
    assert_eq!(refined.try_const_eval(&zero_value), Some(false));

    // Test with negative (should NOT satisfy)
    let negative_value = HirExpr {
        kind: HirExprKind::Integer(-5),
        ty: TypeId::I64,
    };
    assert_eq!(refined.try_const_eval(&negative_value), Some(false));

    // Test with variable (cannot evaluate at compile time)
    let variable_value = HirExpr {
        kind: HirExprKind::Local(1),
        ty: TypeId::I64,
    };
    assert_eq!(refined.try_const_eval(&variable_value), None);
}

#[test]
fn test_refined_type_const_eval_range() {
    // CTR-022: Test range predicates
    // Create a refined type: NonNegI64 = i64 where self >= 0
    let refined = HirRefinedType {
        name: "NonNegI64".to_string(),
        base_type: TypeId::I64,
        predicate: HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::GtEq,
                left: Box::new(HirExpr {
                    kind: HirExprKind::Local(0), // self
                    ty: TypeId::I64,
                }),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Integer(0),
                    ty: TypeId::I64,
                }),
            },
            ty: TypeId::BOOL,
        },
    };

    // Test edge case: 0 should satisfy >= 0
    let zero_value = HirExpr {
        kind: HirExprKind::Integer(0),
        ty: TypeId::I64,
    };
    assert_eq!(refined.try_const_eval(&zero_value), Some(true));

    // Test: -1 should NOT satisfy >= 0
    let negative_value = HirExpr {
        kind: HirExprKind::Integer(-1),
        ty: TypeId::I64,
    };
    assert_eq!(refined.try_const_eval(&negative_value), Some(false));
}

#[test]
fn test_subtype_result_same() {
    // CTR-021: Test SubtypeResult::Same
    let module = HirModule::new();

    // Same types should return Same
    assert_eq!(module.check_subtype(TypeId::I64, TypeId::I64), SubtypeResult::Same);
    assert_eq!(module.check_subtype(TypeId::BOOL, TypeId::BOOL), SubtypeResult::Same);
}

#[test]
fn test_subtype_result_incompatible() {
    // CTR-021: Test SubtypeResult::Incompatible
    let module = HirModule::new();

    // Unrelated types should be incompatible
    assert_eq!(
        module.check_subtype(TypeId::I64, TypeId::BOOL),
        SubtypeResult::Incompatible
    );
    assert_eq!(
        module.check_subtype(TypeId::STRING, TypeId::I64),
        SubtypeResult::Incompatible
    );
}
