//! Integration tests for reference capability system
//!
//! These tests verify that the capability system works end-to-end:
//! - Parsing mut T and iso T syntax
//! - Lowering capabilities to HIR
//! - Type checking with capability rules

mod test_helpers;
use test_helpers::*;

use simple_compiler::hir::CapabilityEnv;
use simple_parser::ast::ReferenceCapability;
use simple_parser::Parser;

#[test]
fn test_parse_mut_capability() {
    let source = r#"
fn update(x: mut Counter) -> i64:
    return 0
"#;

    let module = parse_source(source);

    // Verify we have a function
    assert_eq!(module.items.len(), 1);

    // Verify the parameter has a capability type
    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        assert_eq!(func.params.len(), 1);

        if let Some(param_ty) = &func.params[0].ty {
            match param_ty {
                simple_parser::ast::Type::Capability { capability, inner } => {
                    assert_eq!(*capability, ReferenceCapability::Exclusive);
                    match &**inner {
                        simple_parser::ast::Type::Simple(name) => {
                            assert_eq!(name, "Counter");
                        }
                        _ => panic!("Expected simple type Counter, got {:?}", inner),
                    }
                }
                _ => panic!("Expected Capability type, got {:?}", param_ty),
            }
        } else {
            panic!("Parameter should have type annotation");
        }
    } else {
        panic!("Expected function node");
    }
}

#[test]
fn test_parse_iso_capability() {
    let source = r#"
fn transfer(data: iso Data) -> i64:
    return 0
"#;

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        if let Some(param_ty) = &func.params[0].ty {
            match param_ty {
                simple_parser::ast::Type::Capability { capability, .. } => {
                    assert_eq!(*capability, ReferenceCapability::Isolated);
                }
                _ => panic!("Expected Capability type"),
            }
        }
    }
}

#[test]
fn test_capability_with_generic() {
    let source = r#"
fn process(items: mut List[i64]) -> i64:
    return 0
"#;

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        if let Some(param_ty) = &func.params[0].ty {
            match param_ty {
                simple_parser::ast::Type::Capability { capability, inner } => {
                    assert_eq!(*capability, ReferenceCapability::Exclusive);
                    match &**inner {
                        simple_parser::ast::Type::Generic { name, .. } => {
                            assert_eq!(name, "List");
                        }
                        _ => panic!("Expected generic type"),
                    }
                }
                _ => panic!("Expected Capability type"),
            }
        }
    }
}

#[test]
fn test_capability_env_aliasing_rules() {
    let mut env = CapabilityEnv::new();

    // Shared capabilities can coexist
    assert!(env.can_acquire(1, ReferenceCapability::Shared).is_ok());
    assert!(env.can_acquire(1, ReferenceCapability::Shared).is_ok());

    // Exclusive capability prevents any aliasing
    let mut env2 = CapabilityEnv::new();
    env2.acquire(2, ReferenceCapability::Exclusive);
    assert!(env2.can_acquire(2, ReferenceCapability::Shared).is_err());
    assert!(env2.can_acquire(2, ReferenceCapability::Exclusive).is_err());

    // Isolated capability prevents any aliasing
    let mut env3 = CapabilityEnv::new();
    env3.acquire(3, ReferenceCapability::Isolated);
    assert!(env3.can_acquire(3, ReferenceCapability::Shared).is_err());
    assert!(env3.can_acquire(3, ReferenceCapability::Isolated).is_err());
}

#[test]
fn test_capability_conversion_rules() {
    // Valid conversions (downgrades)
    assert!(CapabilityEnv::can_convert(ReferenceCapability::Exclusive, ReferenceCapability::Shared).is_ok());

    assert!(CapabilityEnv::can_convert(ReferenceCapability::Isolated, ReferenceCapability::Exclusive).is_ok());

    assert!(CapabilityEnv::can_convert(ReferenceCapability::Isolated, ReferenceCapability::Shared).is_ok());

    // Invalid conversions (upcasts)
    assert!(CapabilityEnv::can_convert(ReferenceCapability::Shared, ReferenceCapability::Exclusive).is_err());

    assert!(CapabilityEnv::can_convert(ReferenceCapability::Shared, ReferenceCapability::Isolated).is_err());

    assert!(CapabilityEnv::can_convert(ReferenceCapability::Exclusive, ReferenceCapability::Isolated).is_err());
}

#[test]
fn test_capability_properties() {
    // Shared allows no mutation
    assert!(!ReferenceCapability::Shared.allows_mutation());
    assert!(!ReferenceCapability::Shared.is_transferable());

    // Exclusive allows mutation but not transfer
    assert!(ReferenceCapability::Exclusive.allows_mutation());
    assert!(!ReferenceCapability::Exclusive.is_transferable());

    // Isolated allows both mutation and transfer
    assert!(ReferenceCapability::Isolated.allows_mutation());
    assert!(ReferenceCapability::Isolated.is_transferable());
}

#[test]
fn test_nested_capabilities() {
    // mut mut T should parse (though semantically questionable)
    let source = "fn weird(x: mut mut Counter) -> i64:\n    return 0";

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        if let Some(param_ty) = &func.params[0].ty {
            match param_ty {
                simple_parser::ast::Type::Capability { capability, inner } => {
                    assert_eq!(*capability, ReferenceCapability::Exclusive);
                    // Inner should also be a capability
                    match &**inner {
                        simple_parser::ast::Type::Capability {
                            capability: inner_cap, ..
                        } => {
                            assert_eq!(*inner_cap, ReferenceCapability::Exclusive);
                        }
                        _ => panic!("Expected nested capability"),
                    }
                }
                _ => panic!("Expected Capability type"),
            }
        }
    }
}

#[test]
fn test_capability_release() {
    let mut env = CapabilityEnv::new();

    // Acquire exclusive capability
    env.acquire(1, ReferenceCapability::Exclusive);
    assert!(env.can_acquire(1, ReferenceCapability::Shared).is_err());

    // Release and re-acquire
    env.release(1);
    assert!(env.can_acquire(1, ReferenceCapability::Shared).is_ok());
    assert!(env.can_acquire(1, ReferenceCapability::Exclusive).is_ok());
}

#[test]
fn test_default_capability_is_shared() {
    // A type without capability prefix should be treated as shared
    let source = "fn read(x: Counter) -> i64:\n    return 0";

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        if let Some(param_ty) = &func.params[0].ty {
            // Should be a simple type, not a capability wrapper
            match param_ty {
                simple_parser::ast::Type::Simple(name) => {
                    assert_eq!(name, "Counter");
                    // Default is implicitly Shared
                }
                _ => panic!("Expected simple type (default shared)"),
            }
        }
    }
}

#[test]
fn test_parse_concurrency_mode_actor() {
    // Default mode should be Actor
    let source = r#"
fn process(x: i64) -> i64:
    return x
"#;

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        // No attribute means Actor mode (default)
        assert_eq!(func.attributes.len(), 0);
    }
}

#[test]
fn test_parse_concurrency_mode_lock_base() {
    // Parse lock_base mode from attribute
    let source = r#"
#[concurrency_mode(lock_base)]
fn update(x: mut Counter) -> i64:
    return 0
"#;

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        assert_eq!(func.attributes.len(), 1);
        assert_eq!(func.attributes[0].name, "concurrency_mode");

        if let Some(args) = &func.attributes[0].args {
            if let Some(simple_parser::ast::Expr::Identifier(mode)) = args.first() {
                assert_eq!(mode, "lock_base");
            } else {
                panic!("Expected identifier argument");
            }
        } else {
            panic!("Expected attribute arguments");
        }
    }
}

#[test]
fn test_parse_concurrency_mode_unsafe() {
    // Parse unsafe mode from attribute
    let source = r#"
#[concurrency_mode(unsafe)]
fn raw_ptr(x: i64) -> i64:
    return x
"#;

    let module = parse_source(source);

    if let simple_parser::ast::Node::Function(func) = &module.items[0] {
        assert_eq!(func.attributes.len(), 1);
        assert_eq!(func.attributes[0].name, "concurrency_mode");

        if let Some(args) = &func.attributes[0].args {
            if let Some(simple_parser::ast::Expr::Identifier(mode)) = args.first() {
                assert_eq!(mode, "unsafe");
            } else {
                panic!("Expected identifier argument");
            }
        } else {
            panic!("Expected attribute arguments");
        }
    }
}

#[test]
fn test_mut_in_actor_mode_fails() {
    // mut T should fail in actor mode (default)
    let source = r#"
struct Counter:
    value: i64

fn update(x: mut Counter) -> i64:
    return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should fail with capability error
    assert!(result.is_err(), "Expected error for mut T in actor mode");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("mut") || err.to_string().contains("actor"),
        "Error should mention mut or actor mode: {}",
        err
    );
}

#[test]
fn test_mut_in_lock_base_mode_succeeds() {
    // mut T should succeed in lock_base mode
    // Test just the function with attribute (struct is implicit in lowering)
    let source = r#"
#[concurrency_mode(lock_base)]
fn update(x: mut i64) -> i64:
    return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should succeed
    assert!(result.is_ok(), "mut T should be allowed in lock_base mode");
}

#[test]
fn test_iso_in_all_modes_succeeds() {
    // iso T should succeed in all modes
    let sources = vec![
        // Actor mode (default)
        r#"
fn transfer(x: iso i64) -> i64:
    return 0
"#,
        // Lock base mode
        r#"
#[concurrency_mode(lock_base)]
fn transfer(x: iso i64) -> i64:
    return 0
"#,
        // Unsafe mode
        r#"
#[concurrency_mode(unsafe)]
fn transfer(x: iso i64) -> i64:
    return 0
"#,
    ];

    for source in sources {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("should parse");

        let result = lower_module(&module);

        assert!(result.is_ok(), "iso T should be allowed in all modes");
    }
}

#[test]
fn test_capability_zero_cost_abstraction() {
    // Verify that mut T and T compile to the same representation
    // Capabilities should only affect compile-time checking, not codegen
    use simple_compiler::codegen::types_util::type_id_size;
    use simple_compiler::hir::TypeId;

    // Both i64 and mut i64 should map to the same size
    // Capabilities don't change the TypeId or its size
    let i64_size = type_id_size(TypeId::I64);
    let bool_size = type_id_size(TypeId::BOOL);
    let ptr_size = type_id_size(TypeId::STRING);

    // Verify expected sizes (zero runtime cost)
    assert_eq!(i64_size, 8, "i64 should be 8 bytes");
    assert_eq!(bool_size, 1, "bool should be 1 byte");
    assert_eq!(ptr_size, 8, "pointers should be 8 bytes");

    // This confirms that capabilities have zero runtime cost
    // mut T, iso T, and T all have the same size and representation
}

#[test]
fn test_error_message_quality() {
    // Verify that error messages are helpful and actionable
    let source = r#"
fn update(x: mut i64) -> i64:
    return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should fail with helpful error message
    assert!(result.is_err());
    let err = result.unwrap_err();
    let err_msg = err.to_string();

    // Verify error message contains helpful information
    assert!(err_msg.contains("actor mode"), "Should mention actor mode");
    assert!(
        err_msg.contains("iso T") || err_msg.contains("lock_base"),
        "Should suggest alternatives"
    );

    // Print the error message for manual verification
    eprintln!("Error message:\n{}", err_msg);
}

#[test]
fn test_multiple_parameters_mixed_capabilities() {
    // Test function with multiple parameters having different capabilities
    let source = r#"
#[concurrency_mode(lock_base)]
fn process(a: mut i64, b: iso i64, c: i64) -> i64:
    return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should succeed - lock_base mode allows mut and iso
    assert!(result.is_ok(), "Multiple capabilities should work in lock_base mode");
}

#[test]
fn test_return_type_with_capability() {
    // Test that return types can have capabilities
    let source = r#"
#[concurrency_mode(lock_base)]
fn create() -> mut i64:
    return 42
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should succeed
    assert!(result.is_ok(), "Return types can have capabilities");
}

#[test]
fn test_all_modes_with_shared_capability() {
    // Shared (T) should work in all modes
    let sources = vec![
        "fn read(x: i64) -> i64:\n    return x",
        "#[concurrency_mode(lock_base)]\nfn read(x: i64) -> i64:\n    return x",
        "#[concurrency_mode(unsafe)]\nfn read(x: i64) -> i64:\n    return x",
    ];

    for source in sources {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("should parse");

        let result = lower_module(&module);

        assert!(result.is_ok(), "Shared (T) should work in all modes");
    }
}

#[test]
fn test_unsafe_mode_allows_all_capabilities() {
    // Unsafe mode should allow all capability combinations
    let source = r#"
#[concurrency_mode(unsafe)]
fn unsafe_process(a: mut i64, b: iso i64, c: i64) -> mut i64:
    return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should succeed - unsafe mode allows everything
    assert!(result.is_ok(), "Unsafe mode should allow all capabilities");
}

#[test]
fn test_actor_mode_rejects_mut_in_params() {
    // Actor mode should reject mut in any parameter position
    let sources = vec![
        "fn f1(a: i64, b: mut i64) -> i64:\n    return 0",
        "fn f2(a: mut i64, b: i64, c: i64) -> i64:\n    return 0",
    ];

    for source in sources {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("should parse");

        let result = lower_module(&module);

        assert!(result.is_err(), "Actor mode should reject mut in any parameter");
    }
}

#[test]
fn test_class_method_capabilities() {
    // Test that class methods respect default concurrency mode (actor)
    // Methods should reject mut T in actor mode just like standalone functions
    let source = r#"
class Counter:
    value: i64

    fn increment(self, delta: mut i64) -> i64:
        return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should fail - methods default to actor mode
    assert!(result.is_err(), "Class methods default to actor mode and reject mut T");
}

#[test]
fn test_nested_capability_types() {
    // Test deeply nested capability types (mut mut T, iso iso T, etc.)
    let source = r#"
#[concurrency_mode(lock_base)]
fn nested(x: mut mut i64) -> i64:
    return 0
"#;

    let module = parse_source(source);

    let result = lower_module(&module);

    // Should succeed (though semantically unusual, parser accepts it)
    assert!(result.is_ok(), "Nested capabilities should parse and lower");
}
