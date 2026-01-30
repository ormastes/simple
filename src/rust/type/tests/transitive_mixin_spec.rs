// Transitive Mixin Dependency Resolution Specification Tests
//
// Tests for transitive mixin dependency resolution:
// - BFS-based transitive resolution
// - Diamond dependency deduplication
// - Transitive field access
// - Transitive method resolution
// - Mixin trait requirement propagation

use simple_type::{MixinInfo, FunctionType, RequiredMethodSig, Type, TypeChecker};
use std::collections::HashMap;

// Helper to create base mixin with a single field
fn create_base_mixin() -> MixinInfo {
    MixinInfo {
        name: "Base".to_string(),
        type_params: vec![],
        fields: vec![("id".to_string(), Type::Int)],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec![],
        required_methods: vec![],
    }
}

// Helper to create timestamped mixin that requires Base
fn create_timestamped_mixin() -> MixinInfo {
    MixinInfo {
        name: "Timestamped".to_string(),
        type_params: vec![],
        fields: vec![
            ("created_at".to_string(), Type::Int),
            ("updated_at".to_string(), Type::Int),
        ],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec!["Base".to_string()],
        required_methods: vec![],
    }
}

// Helper to create versioned mixin that requires Timestamped
fn create_versioned_mixin() -> MixinInfo {
    MixinInfo {
        name: "Versioned".to_string(),
        type_params: vec![],
        fields: vec![("version".to_string(), Type::Int)],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec!["Timestamped".to_string()],
        required_methods: vec![],
    }
}

#[test]
fn test_transitive_empty_queue() {
    // Resolving empty mixin list returns empty result
    let checker = TypeChecker::new();
    let result = checker.resolve_transitive_mixins(&[]);
    assert_eq!(result, Vec::<String>::new(), "Empty input should return empty result");
}

#[test]
fn test_transitive_single_mixin_no_deps() {
    // Single mixin with no dependencies returns just that mixin
    let mut checker = TypeChecker::new();
    let base = create_base_mixin();
    checker.mixins.insert("Base".to_string(), base);

    let result = checker.resolve_transitive_mixins(&["Base".to_string()]);
    assert_eq!(result, vec!["Base".to_string()], "Single mixin with no deps");
}

#[test]
fn test_transitive_two_level_chain() {
    // Timestamped requires Base → should return [Timestamped, Base]
    let mut checker = TypeChecker::new();
    checker.mixins.insert("Base".to_string(), create_base_mixin());
    checker.mixins.insert("Timestamped".to_string(), create_timestamped_mixin());

    let result = checker.resolve_transitive_mixins(&["Timestamped".to_string()]);
    assert_eq!(result.len(), 2, "Should resolve 2 mixins");
    assert!(result.contains(&"Timestamped".to_string()), "Should contain Timestamped");
    assert!(result.contains(&"Base".to_string()), "Should contain Base");
}

#[test]
fn test_transitive_three_level_chain() {
    // Versioned requires Timestamped requires Base → [Versioned, Timestamped, Base]
    let mut checker = TypeChecker::new();
    checker.mixins.insert("Base".to_string(), create_base_mixin());
    checker.mixins.insert("Timestamped".to_string(), create_timestamped_mixin());
    checker.mixins.insert("Versioned".to_string(), create_versioned_mixin());

    let result = checker.resolve_transitive_mixins(&["Versioned".to_string()]);
    assert_eq!(result.len(), 3, "Should resolve 3 mixins");
    assert!(result.contains(&"Versioned".to_string()), "Should contain Versioned");
    assert!(result.contains(&"Timestamped".to_string()), "Should contain Timestamped");
    assert!(result.contains(&"Base".to_string()), "Should contain Base");
}

#[test]
fn test_transitive_diamond_dependency() {
    // Diamond: Combined requires Left and Right, both require Base
    // Should return [Combined, Left, Right, Base] with Base appearing once
    let mut checker = TypeChecker::new();

    let base = create_base_mixin();
    let left = MixinInfo {
        name: "Left".to_string(),
        type_params: vec![],
        fields: vec![("left_field".to_string(), Type::Int)],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec!["Base".to_string()],
        required_methods: vec![],
    };
    let right = MixinInfo {
        name: "Right".to_string(),
        type_params: vec![],
        fields: vec![("right_field".to_string(), Type::Str)],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec!["Base".to_string()],
        required_methods: vec![],
    };
    let combined = MixinInfo {
        name: "Combined".to_string(),
        type_params: vec![],
        fields: vec![],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec!["Left".to_string(), "Right".to_string()],
        required_methods: vec![],
    };

    checker.mixins.insert("Base".to_string(), base);
    checker.mixins.insert("Left".to_string(), left);
    checker.mixins.insert("Right".to_string(), right);
    checker.mixins.insert("Combined".to_string(), combined);

    let result = checker.resolve_transitive_mixins(&["Combined".to_string()]);
    assert_eq!(result.len(), 4, "Should resolve 4 unique mixins");
    assert!(result.contains(&"Combined".to_string()), "Should contain Combined");
    assert!(result.contains(&"Left".to_string()), "Should contain Left");
    assert!(result.contains(&"Right".to_string()), "Should contain Right");
    assert!(result.contains(&"Base".to_string()), "Should contain Base");

    // Base should appear exactly once (deduplication)
    let base_count = result.iter().filter(|&x| x == "Base").count();
    assert_eq!(base_count, 1, "Base should appear exactly once (diamond deduplication)");
}

#[test]
fn test_transitive_mixin_not_found() {
    // Requesting non-existent mixin should return empty (graceful handling)
    let checker = TypeChecker::new();
    let result = checker.resolve_transitive_mixins(&["NonExistent".to_string()]);
    assert_eq!(result, Vec::<String>::new(), "Non-existent mixin should return empty");
}

#[test]
fn test_transitive_partial_resolution() {
    // If middle mixin is missing, should still resolve what's available
    let mut checker = TypeChecker::new();
    checker.mixins.insert("Base".to_string(), create_base_mixin());
    // Timestamped is missing!
    checker.mixins.insert("Versioned".to_string(), create_versioned_mixin());

    let result = checker.resolve_transitive_mixins(&["Versioned".to_string()]);
    // Should get Versioned, but not Timestamped or Base (chain broken)
    assert!(result.contains(&"Versioned".to_string()), "Should contain Versioned");
    assert!(!result.contains(&"Base".to_string()), "Should NOT contain Base (chain broken)");
}

#[test]
fn test_transitive_field_resolution_simple() {
    // get_all_fields should return fields from transitive mixins
    let mut checker = TypeChecker::new();
    checker.mixins.insert("Base".to_string(), create_base_mixin());

    // Register composition: type "Document" uses "Base"
    let mixin_ref = simple_parser::MixinRef {
        span: simple_parser::Span::new(0, 0, 0, 0),
        name: "Base".to_string(),
        type_args: vec![],
        overrides: vec![],
    };
    checker.compositions.insert("Document".to_string(), vec![mixin_ref]);

    let fields = checker.get_all_fields("Document");
    assert_eq!(fields.len(), 1, "Should have 1 field from Base");
    assert_eq!(fields[0].0, "id");
    assert_eq!(fields[0].1, Type::Int);
}

#[test]
fn test_transitive_field_resolution_two_level() {
    // get_all_fields should return fields from 2-level mixin chain
    let mut checker = TypeChecker::new();
    checker.mixins.insert("Base".to_string(), create_base_mixin());
    checker.mixins.insert("Timestamped".to_string(), create_timestamped_mixin());

    // Register composition: type "Document" uses "Timestamped"
    let mixin_ref = simple_parser::MixinRef {
        span: simple_parser::Span::new(0, 0, 0, 0),
        name: "Timestamped".to_string(),
        type_args: vec![],
        overrides: vec![],
    };
    checker.compositions.insert("Document".to_string(), vec![mixin_ref]);

    let fields = checker.get_all_fields("Document");
    // Should have: id (Base), created_at, updated_at (Timestamped)
    assert_eq!(fields.len(), 3, "Should have 3 fields total");

    let field_names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
    assert!(field_names.contains(&"id"), "Should have id from Base");
    assert!(field_names.contains(&"created_at"), "Should have created_at from Timestamped");
    assert!(field_names.contains(&"updated_at"), "Should have updated_at from Timestamped");
}

#[test]
fn test_transitive_field_resolution_three_level() {
    // get_all_fields should return fields from 3-level mixin chain
    let mut checker = TypeChecker::new();
    checker.mixins.insert("Base".to_string(), create_base_mixin());
    checker.mixins.insert("Timestamped".to_string(), create_timestamped_mixin());
    checker.mixins.insert("Versioned".to_string(), create_versioned_mixin());

    // Register composition: type "Document" uses "Versioned"
    let mixin_ref = simple_parser::MixinRef {
        span: simple_parser::Span::new(0, 0, 0, 0),
        name: "Versioned".to_string(),
        type_args: vec![],
        overrides: vec![],
    };
    checker.compositions.insert("Document".to_string(), vec![mixin_ref]);

    let fields = checker.get_all_fields("Document");
    // Should have: id (Base), created_at, updated_at (Timestamped), version (Versioned)
    assert_eq!(fields.len(), 4, "Should have 4 fields total");

    let field_names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
    assert!(field_names.contains(&"id"), "Should have id from Base");
    assert!(field_names.contains(&"created_at"), "Should have created_at from Timestamped");
    assert!(field_names.contains(&"updated_at"), "Should have updated_at from Timestamped");
    assert!(field_names.contains(&"version"), "Should have version from Versioned");
}

#[test]
fn test_transitive_with_generic_mixin() {
    // Generic mixin Container[T] with transitive resolution
    let mut checker = TypeChecker::new();

    let container = MixinInfo {
        name: "Container".to_string(),
        type_params: vec!["T".to_string()],
        fields: vec![("value".to_string(), Type::TypeParam("T".to_string()))],
        methods: vec![],
        required_traits: vec![],
        required_mixins: vec![],
        required_methods: vec![],
    };

    checker.mixins.insert("Container".to_string(), container);

    // Register composition with type args: Container[i64]
    let mixin_ref = simple_parser::MixinRef {
        span: simple_parser::Span::new(0, 0, 0, 0),
        name: "Container".to_string(),
        type_args: vec![simple_parser::ast::Type::Simple("i64".to_string())],
        overrides: vec![],
    };
    checker.compositions.insert("MyType".to_string(), vec![mixin_ref]);

    let fields = checker.get_all_fields("MyType");
    assert_eq!(fields.len(), 1, "Should have 1 field");
    assert_eq!(fields[0].0, "value");
    assert_eq!(fields[0].1, Type::Int, "Type param T should be substituted with Int");
}

#[test]
fn test_mixin_instantiate_preserves_required_mixins() {
    // Verify that instantiate() carries over required_mixins
    let mixin = MixinInfo {
        name: "Test".to_string(),
        type_params: vec!["T".to_string()],
        fields: vec![("field".to_string(), Type::TypeParam("T".to_string()))],
        methods: vec![],
        required_traits: vec!["Show".to_string()],
        required_mixins: vec!["Base".to_string()],
        required_methods: vec![],
    };

    let instantiated = mixin.instantiate(&[Type::Int]).expect("Should instantiate");

    assert_eq!(instantiated.required_mixins, vec!["Base".to_string()],
        "required_mixins should be preserved after instantiation");
    assert_eq!(instantiated.required_traits, vec!["Show".to_string()],
        "required_traits should also be preserved");
}
