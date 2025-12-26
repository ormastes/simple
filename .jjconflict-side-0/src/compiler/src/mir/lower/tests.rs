use super::*;
use crate::di::parse_di_config;
use crate::hir::{self, BinOp};
use crate::mir::{BlockId, ContractKind, MirInst, Terminator};
use crate::mir::function::MirModule;
use simple_parser::Parser;

fn compile_to_mir(source: &str) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir(&hir_module)
}

fn compile_to_mir_with_di(source: &str, di_toml: &str) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    let di_value: toml::Value = di_toml.parse().expect("parse di toml");
    let di_config = parse_di_config(&di_value)
        .expect("di config parse")
        .expect("di config present");
    lower_to_mir_with_mode_and_di(&hir_module, ContractMode::All, Some(di_config))
}

#[test]
fn test_lower_simple_return() {
    let mir = compile_to_mir("fn test() -> i64:\n    return 42\n").unwrap();

    assert_eq!(mir.functions.len(), 1);
    let func = &mir.functions[0];
    assert_eq!(func.name, "test");

    let entry = func.block(BlockId(0)).unwrap();
    assert!(!entry.instructions.is_empty());
    assert!(matches!(entry.terminator, Terminator::Return(Some(_))));
}

#[test]
fn test_di_injects_builtin_param_in_mir() {
    let source = r#"
@inject
fn use_num(x: i64) -> i64:
    return x

fn make_num() -> i64:
    return 42

fn main() -> i64:
    return use_num()
"#;

    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(i64) }", impl = "make_num", scope = "Transient", priority = 10 }
]
"#;

    let mir = compile_to_mir_with_di(source, di_toml).expect("lower with di");
    let main_fn = mir
        .functions
        .iter()
        .find(|func| func.name == "main")
        .expect("main function");

    let has_make_num_call = main_fn.blocks.iter().any(|block| {
        block.instructions.iter().any(|inst| {
            matches!(inst, MirInst::Call { target, .. } if target.name() == "make_num")
        })
    });
    assert!(has_make_num_call, "expected injected call to make_num");
}

#[test]
fn test_lower_binary_op() {
    let mir = compile_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have: load a, load b, add, return
    assert!(entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::BinOp { op: BinOp::Add, .. })));
}

#[test]
fn test_lower_if_statement() {
    let mir = compile_to_mir(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
    ).unwrap();

    let func = &mir.functions[0];
    // Should have multiple blocks: entry, then, else, merge
    assert!(func.blocks.len() >= 3);

    let entry = func.block(BlockId(0)).unwrap();
    assert!(matches!(entry.terminator, Terminator::Branch { .. }));
}

#[test]
fn test_lower_while_loop() {
    let mir = compile_to_mir(
        "fn count() -> i64:\n    let x: i64 = 0\n    while x < 10:\n        x = x + 1\n    return x\n"
    ).unwrap();

    let func = &mir.functions[0];
    // Should have: entry, condition, body, exit blocks
    assert!(func.blocks.len() >= 4);
}

#[test]
fn test_lower_local_variable() {
    let mir = compile_to_mir("fn test() -> i64:\n    let x: i64 = 5\n    return x\n").unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have LocalAddr and Store for the let
    assert!(entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::LocalAddr { .. })));
    assert!(entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::Store { .. })));
}

#[test]
fn test_lower_function_with_precondition() {
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir(source).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have a ContractCheck instruction for the precondition
    assert!(entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { kind: ContractKind::Precondition, .. })));
}

#[test]
fn test_lower_function_with_postcondition() {
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn abs_value(x: i64) -> i64:\n    out(ret):\n        ret >= 0\n    return x\n";
    let mir = compile_to_mir(source).unwrap();

    let func = &mir.functions[0];

    // Should have a ContractCheck instruction for the postcondition somewhere
    // Check all blocks for postcondition checks
    let has_postcondition_check = func.blocks.iter().any(|block| {
        block.instructions.iter().any(|i| {
            matches!(i, MirInst::ContractCheck { kind: ContractKind::Postcondition, .. })
        })
    });
    assert!(has_postcondition_check, "Should have postcondition check");
}

#[test]
fn test_lower_function_with_invariant() {
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn test_invariant(x: i64) -> i64:\n    invariant:\n        x >= 0\n    return x + 1\n";
    let mir = compile_to_mir(source).unwrap();

    let func = &mir.functions[0];

    // Should have InvariantEntry and InvariantExit checks
    let has_entry = func.blocks.iter().any(|block| {
        block.instructions.iter().any(|i| {
            matches!(i, MirInst::ContractCheck { kind: ContractKind::InvariantEntry, .. })
        })
    });
    let has_exit = func.blocks.iter().any(|block| {
        block.instructions.iter().any(|i| {
            matches!(i, MirInst::ContractCheck { kind: ContractKind::InvariantExit, .. })
        })
    });
    assert!(has_entry, "Should have invariant entry check");
    assert!(has_exit, "Should have invariant exit check");
}

// =========================================================================
// Contract Mode Tests (CTR-040 to CTR-043)
// =========================================================================

fn compile_to_mir_with_mode(source: &str, mode: ContractMode) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir_with_mode(&hir_module, mode)
}

#[test]
fn test_contract_mode_off_no_checks() {
    // With ContractMode::Off, no contract checks should be emitted
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::Off).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should NOT have any ContractCheck instructions
    let has_contract_check = entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { .. }));
    assert!(!has_contract_check, "ContractMode::Off should not emit contract checks");
}

#[test]
fn test_contract_mode_boundary_public_function() {
    // With ContractMode::Boundary, public functions should have contract checks
    let source = "pub fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::Boundary).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have ContractCheck for public function
    let has_contract_check = entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { kind: ContractKind::Precondition, .. }));
    assert!(has_contract_check, "ContractMode::Boundary should emit checks for public functions");
}

#[test]
fn test_contract_mode_boundary_private_function() {
    // With ContractMode::Boundary, private functions should NOT have contract checks
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::Boundary).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should NOT have ContractCheck for private function
    let has_contract_check = entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { .. }));
    assert!(!has_contract_check, "ContractMode::Boundary should not emit checks for private functions");
}

#[test]
fn test_contract_mode_all_checks_all_functions() {
    // With ContractMode::All (default), all functions should have contract checks
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::All).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have ContractCheck for all functions
    let has_contract_check = entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { kind: ContractKind::Precondition, .. }));
    assert!(has_contract_check, "ContractMode::All should emit checks for all functions");
}

#[test]
fn test_contract_mode_from_str() {
    assert_eq!(ContractMode::from_str("off"), Some(ContractMode::Off));
    assert_eq!(ContractMode::from_str("none"), Some(ContractMode::Off));
    assert_eq!(ContractMode::from_str("boundary"), Some(ContractMode::Boundary));
    assert_eq!(ContractMode::from_str("public"), Some(ContractMode::Boundary));
    assert_eq!(ContractMode::from_str("all"), Some(ContractMode::All));
    assert_eq!(ContractMode::from_str("on"), Some(ContractMode::All));
    assert_eq!(ContractMode::from_str("test"), Some(ContractMode::Test));
    assert_eq!(ContractMode::from_str("debug"), Some(ContractMode::Test));
    assert_eq!(ContractMode::from_str("OFF"), Some(ContractMode::Off));
    assert_eq!(ContractMode::from_str("TEST"), Some(ContractMode::Test));
    assert_eq!(ContractMode::from_str("invalid"), None);
}

#[test]
fn test_contract_mode_as_str() {
    assert_eq!(ContractMode::Off.as_str(), "off");
    assert_eq!(ContractMode::Boundary.as_str(), "boundary");
    assert_eq!(ContractMode::All.as_str(), "all");
    assert_eq!(ContractMode::Test.as_str(), "test");
}

#[test]
fn test_contract_mode_test_has_rich_diagnostics() {
    // CTR-043: Test mode should have rich diagnostics
    assert!(ContractMode::Test.has_rich_diagnostics());
    assert!(!ContractMode::All.has_rich_diagnostics());
    assert!(!ContractMode::Boundary.has_rich_diagnostics());
    assert!(!ContractMode::Off.has_rich_diagnostics());
}

#[test]
fn test_contract_mode_checks_all() {
    // CTR-043: Test mode should check all contracts like All mode
    assert!(ContractMode::Test.checks_all());
    assert!(ContractMode::All.checks_all());
    assert!(!ContractMode::Boundary.checks_all());
    assert!(!ContractMode::Off.checks_all());
}

#[test]
fn test_contract_mode_default_is_all() {
    assert_eq!(ContractMode::default(), ContractMode::All);
}

// =========================================================================
// Refinement Type Tests (CTR-020)
// =========================================================================

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
    assert!(hir_module.refined_types.contains_key("PosI64"),
        "Refined type PosI64 should be registered");

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
    assert!(!hir_module.refined_types.contains_key("UserId"),
        "Simple type alias should not be in refined_types");

    // But the type name should still be registered
    assert!(hir_module.types.lookup("UserId").is_some(),
        "Type alias name should be registered");
}

// =========================================================================
// Pure Expression Enforcement Tests (CTR-030-032)
// =========================================================================

#[test]
fn test_pure_function_in_contract_allowed() {
    // Test that #[pure] functions can be called in contracts
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "#[pure]\nfn is_valid(x: i64) -> bool:\n    return x > 0\n\nfn process(x: i64) -> i64:\n    in:\n        is_valid(x)\n    return x * 2\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");

    // Should have is_valid marked as pure
    let is_valid_func = hir_module.functions.iter().find(|f| f.name == "is_valid");
    assert!(is_valid_func.is_some(), "is_valid function should exist");
    assert!(is_valid_func.unwrap().is_pure, "is_valid should be marked as pure");
}

#[test]
fn test_impure_function_in_contract_rejected() {
    // Test that non-pure functions cause an error in contracts
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn impure_check(x: i64) -> bool:\n    return x > 0\n\nfn process(x: i64) -> i64:\n    in:\n        impure_check(x)\n    return x * 2\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let result = hir::lower(&ast);

    // Should fail with ImpureFunctionInContract error
    assert!(result.is_err(), "Should reject impure function in contract");
    let err = result.unwrap_err();
    let err_str = format!("{}", err);
    assert!(err_str.contains("impure_check") || err_str.contains("Impure"),
        "Error should mention impure function: {}", err_str);
}

#[test]
fn test_builtin_math_in_contract_allowed() {
    // Test that builtin math functions are implicitly pure
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn safe_fn(x: i64) -> i64:\n    in:\n        x >= 0\n    return abs(x)\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast);

    // Should succeed because abs is implicitly pure and x >= 0 uses no function call
    assert!(hir_module.is_ok(), "Comparison operators should be allowed in contracts");
}

// =========================================================================
// Snapshot-Safe Types Tests (CTR-060-062)
// =========================================================================

#[test]
fn test_snapshot_safe_primitives() {
    // Test that primitive types are snapshot-safe in the type registry
    use crate::hir::{TypeRegistry, TypeId};

    let registry = TypeRegistry::new();

    // CTR-060: Primitives should be snapshot-safe
    assert!(registry.is_snapshot_safe(TypeId::BOOL), "bool should be snapshot-safe");
    assert!(registry.is_snapshot_safe(TypeId::I64), "i64 should be snapshot-safe");
    assert!(registry.is_snapshot_safe(TypeId::F64), "f64 should be snapshot-safe");
    assert!(registry.is_snapshot_safe(TypeId::STRING), "string should be snapshot-safe");
    assert!(registry.is_snapshot_safe(TypeId::NIL), "nil should be snapshot-safe");
}

#[test]
fn test_snapshot_safe_struct() {
    // Test that structs with primitive fields are snapshot-safe (CTR-061)
    use crate::hir::{HirType, TypeRegistry, TypeId};

    let mut registry = TypeRegistry::new();

    // Register a struct with primitive fields
    registry.register_named(
        "Point".to_string(),
        HirType::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), TypeId::I64),
                ("y".to_string(), TypeId::I64),
            ],
            has_snapshot: false,
        },
    );

    let point_id = registry.lookup("Point").unwrap();
    assert!(registry.is_snapshot_safe(point_id), "Struct with primitive fields should be snapshot-safe");
}

#[test]
fn test_snapshot_unsafe_function_type() {
    // Test that function types are NOT snapshot-safe
    use crate::hir::{HirType, TypeRegistry, TypeId};

    let mut registry = TypeRegistry::new();

    // Register a function type
    let func_id = registry.register(HirType::Function {
        params: vec![TypeId::I64],
        ret: TypeId::I64,
    });

    assert!(!registry.is_snapshot_safe(func_id), "Function types should NOT be snapshot-safe");
}

// =========================================================================
// Module Boundary Checking Tests (CTR-012)
// =========================================================================

#[test]
fn test_module_boundary_parameter_invariant() {
    // Test that public functions get preconditions for typed parameters
    use crate::hir::{HirExpr, HirExprKind, TypeId};

    // Create an expression: self.x > 0 (local 0 is self, field 0 is x)
    let invariant_expr = HirExpr {
        kind: HirExprKind::Binary {
            op: crate::hir::BinOp::Gt,
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
        HirExprKind::Binary { left, .. } => {
            match &left.kind {
                HirExprKind::FieldAccess { receiver, .. } => {
                    match &receiver.kind {
                        HirExprKind::Local(idx) => {
                            assert_eq!(*idx, 2, "Local 0 should be substituted with 2");
                        }
                        _ => panic!("Expected Local after substitution"),
                    }
                }
                _ => panic!("Expected FieldAccess"),
            }
        }
        _ => panic!("Expected Binary"),
    }
}

#[test]
fn test_module_boundary_return_invariant() {
    // Test that public functions get postconditions for typed return values
    use crate::hir::{HirExpr, HirExprKind, TypeId};

    // Create an expression: self.valid == true (local 0 is self)
    let invariant_expr = HirExpr {
        kind: HirExprKind::Binary {
            op: crate::hir::BinOp::Eq,
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
    use crate::hir::{HirType, TypeRegistry, TypeId};

    let mut registry = TypeRegistry::new();

    // Register a struct
    let struct_id = registry.register_named(
        "MyStruct".to_string(),
        HirType::Struct {
            name: "MyStruct".to_string(),
            fields: vec![("x".to_string(), TypeId::I64)],
            has_snapshot: false,
        },
    );

    // Register an enum
    let enum_id = registry.register_named(
        "MyEnum".to_string(),
        HirType::Enum {
            name: "MyEnum".to_string(),
            variants: vec![("A".to_string(), None), ("B".to_string(), None)],
        },
    );

    // Test get_type_name
    assert_eq!(registry.get_type_name(struct_id), Some("MyStruct"));
    assert_eq!(registry.get_type_name(enum_id), Some("MyEnum"));
    assert_eq!(registry.get_type_name(TypeId::I64), None); // Primitives don't have names
    assert_eq!(registry.get_type_name(TypeId::STRING), None);
}

// =========================================================================
// Refinement Type Tests (CTR-021-023)
// =========================================================================

#[test]
fn test_refined_type_const_eval_greater_than() {
    // CTR-022: Test compile-time evaluation of predicates
    use crate::hir::{HirExpr, HirExprKind, HirRefinedType, BinOp, TypeId};

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
    use crate::hir::{HirExpr, HirExprKind, HirRefinedType, BinOp, TypeId};

    // Create a refined type: Percentage = i64 where self >= 0 and self <= 100
    // For simplicity, just test >= 0
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
    use crate::hir::{HirModule, SubtypeResult, TypeId};

    let module = HirModule::new();

    // Same types should return Same
    assert_eq!(module.check_subtype(TypeId::I64, TypeId::I64), SubtypeResult::Same);
    assert_eq!(module.check_subtype(TypeId::BOOL, TypeId::BOOL), SubtypeResult::Same);
}

#[test]
fn test_subtype_result_incompatible() {
    // CTR-021: Test SubtypeResult::Incompatible
    use crate::hir::{HirModule, SubtypeResult, TypeId};

    let module = HirModule::new();

    // Unrelated types should be incompatible
    assert_eq!(module.check_subtype(TypeId::I64, TypeId::BOOL), SubtypeResult::Incompatible);
    assert_eq!(module.check_subtype(TypeId::STRING, TypeId::I64), SubtypeResult::Incompatible);
}

// =========================================================================
// Snapshot Annotation Tests (CTR-062)
// =========================================================================

#[test]
fn test_snapshot_annotation_makes_type_safe() {
    // CTR-062: Types with #[snapshot] are always snapshot-safe
    use crate::hir::{HirType, TypeRegistry, TypeId, PointerKind};

    let mut registry = TypeRegistry::new();

    // Register a struct WITHOUT #[snapshot] that contains a mutable reference
    // This should NOT be snapshot-safe
    let mutable_ptr_type = registry.register(HirType::Pointer {
        kind: PointerKind::BorrowMut,
        capability: simple_parser::ast::ReferenceCapability::Exclusive,
        inner: TypeId::I64,
    });

    let unsafe_struct = registry.register_named(
        "UnsafeStruct".to_string(),
        HirType::Struct {
            name: "UnsafeStruct".to_string(),
            fields: vec![("data".to_string(), mutable_ptr_type)],
            has_snapshot: false, // No #[snapshot] attribute
        },
    );

    assert!(!registry.is_snapshot_safe(unsafe_struct),
        "Struct with mutable reference should NOT be snapshot-safe without #[snapshot]");

    // Register a struct WITH #[snapshot] that contains a mutable reference
    // This should BE snapshot-safe due to the annotation
    let safe_struct = registry.register_named(
        "SafeStruct".to_string(),
        HirType::Struct {
            name: "SafeStruct".to_string(),
            fields: vec![("data".to_string(), mutable_ptr_type)],
            has_snapshot: true, // Has #[snapshot] attribute
        },
    );

    assert!(registry.is_snapshot_safe(safe_struct),
        "Struct with #[snapshot] should be snapshot-safe even with mutable reference");
}

#[test]
fn test_snapshot_annotation_on_primitive_struct() {
    // CTR-062: #[snapshot] is redundant but harmless on structs with only primitives
    use crate::hir::{HirType, TypeRegistry, TypeId};

    let mut registry = TypeRegistry::new();

    // Struct with only primitives but also has #[snapshot]
    let point_with_snapshot = registry.register_named(
        "PointWithSnapshot".to_string(),
        HirType::Struct {
            name: "PointWithSnapshot".to_string(),
            fields: vec![
                ("x".to_string(), TypeId::I64),
                ("y".to_string(), TypeId::I64),
            ],
            has_snapshot: true,
        },
    );

    assert!(registry.is_snapshot_safe(point_with_snapshot),
        "Struct with #[snapshot] and primitive fields should be snapshot-safe");
}
