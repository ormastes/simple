//! Snapshot-safe types tests (CTR-060-062)

use crate::hir::{HirType, PointerKind, TypeId, TypeRegistry};

#[test]
fn test_snapshot_safe_primitives() {
    // Test that primitive types are snapshot-safe in the type registry
    let registry = TypeRegistry::new();

    // CTR-060: Primitives should be snapshot-safe
    assert!(registry.is_snapshot_safe(TypeId::BOOL), "bool should be snapshot-safe");
    assert!(registry.is_snapshot_safe(TypeId::I64), "i64 should be snapshot-safe");
    assert!(registry.is_snapshot_safe(TypeId::F64), "f64 should be snapshot-safe");
    assert!(
        registry.is_snapshot_safe(TypeId::STRING),
        "string should be snapshot-safe"
    );
    assert!(registry.is_snapshot_safe(TypeId::NIL), "nil should be snapshot-safe");
}

#[test]
fn test_snapshot_safe_struct() {
    // Test that structs with primitive fields are snapshot-safe (CTR-061)
    let mut registry = TypeRegistry::new();

    // Register a struct with primitive fields
    registry.register_named(
        "Point".to_string(),
        HirType::Struct {
            name: "Point".to_string(),
            fields: vec![("x".to_string(), TypeId::I64), ("y".to_string(), TypeId::I64)],
            has_snapshot: false,
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: std::collections::HashMap::new(),
        },
    );

    let point_id = registry.lookup("Point").unwrap();
    assert!(
        registry.is_snapshot_safe(point_id),
        "Struct with primitive fields should be snapshot-safe"
    );
}

#[test]
fn test_snapshot_unsafe_function_type() {
    // Test that function types are NOT snapshot-safe
    let mut registry = TypeRegistry::new();

    // Register a function type
    let func_id = registry.register(HirType::Function {
        params: vec![TypeId::I64],
        ret: TypeId::I64,
    });

    assert!(
        !registry.is_snapshot_safe(func_id),
        "Function types should NOT be snapshot-safe"
    );
}

#[test]
fn test_snapshot_annotation_makes_type_safe() {
    // CTR-062: Types with #[snapshot] are always snapshot-safe
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
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: std::collections::HashMap::new(),
        },
    );

    assert!(
        !registry.is_snapshot_safe(unsafe_struct),
        "Struct with mutable reference should NOT be snapshot-safe without #[snapshot]"
    );

    // Register a struct WITH #[snapshot] that contains a mutable reference
    // This should BE snapshot-safe due to the annotation
    let safe_struct = registry.register_named(
        "SafeStruct".to_string(),
        HirType::Struct {
            name: "SafeStruct".to_string(),
            fields: vec![("data".to_string(), mutable_ptr_type)],
            has_snapshot: true, // Has #[snapshot] attribute
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: std::collections::HashMap::new(),
        },
    );

    assert!(
        registry.is_snapshot_safe(safe_struct),
        "Struct with #[snapshot] should be snapshot-safe even with mutable reference"
    );
}

#[test]
fn test_snapshot_annotation_on_primitive_struct() {
    // CTR-062: #[snapshot] is redundant but harmless on structs with only primitives
    let mut registry = TypeRegistry::new();

    // Struct with only primitives but also has #[snapshot]
    let point_with_snapshot = registry.register_named(
        "PointWithSnapshot".to_string(),
        HirType::Struct {
            name: "PointWithSnapshot".to_string(),
            fields: vec![("x".to_string(), TypeId::I64), ("y".to_string(), TypeId::I64)],
            has_snapshot: true,
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: std::collections::HashMap::new(),
        },
    );

    assert!(
        registry.is_snapshot_safe(point_with_snapshot),
        "Struct with #[snapshot] and primitive fields should be snapshot-safe"
    );
}
