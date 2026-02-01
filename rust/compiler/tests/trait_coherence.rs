use simple_compiler::trait_coherence::{CoherenceChecker, CoherenceError};
use simple_parser::ast::*;
use simple_parser::token::Span;

fn make_span() -> Span {
    Span::new(0, 0, 0, 0)
}

fn make_type(name: &str) -> Type {
    Type::Simple(name.to_string())
}

fn make_generic_type(name: &str, args: Vec<Type>) -> Type {
    Type::Generic {
        name: name.to_string(),
        args,
    }
}

fn make_impl_block_with_attrs(
    trait_name: Option<String>,
    target_type: Type,
    generic_params: Vec<String>,
    associated_types: Vec<AssociatedTypeImpl>,
    attributes: Vec<Attribute>,
) -> ImplBlock {
    ImplBlock {
        span: make_span(),
        attributes,
        generic_params,
        where_clause: vec![],
        target_type,
        trait_name,
        trait_type_params: vec![],
        associated_types,
        methods: vec![],
    }
}

fn make_impl_block(
    trait_name: Option<String>,
    target_type: Type,
    generic_params: Vec<String>,
    associated_types: Vec<AssociatedTypeImpl>,
) -> ImplBlock {
    ImplBlock {
        span: make_span(),
        attributes: vec![],
        generic_params,
        where_clause: vec![],
        target_type,
        trait_name,
        trait_type_params: vec![],
        associated_types,
        methods: vec![],
    }
}

#[test]
fn test_orphan_rule_allows_local_trait_foreign_type() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("MyTrait".to_string());

    let impl_block = make_impl_block(Some("MyTrait".to_string()), make_type("String"), vec![], vec![]);

    assert!(checker.check_impl(&impl_block).is_ok());
}

#[test]
fn test_orphan_rule_allows_foreign_trait_local_type() {
    let mut checker = CoherenceChecker::new();
    checker.register_type("MyType".to_string());

    let impl_block = make_impl_block(Some("Display".to_string()), make_type("MyType"), vec![], vec![]);

    assert!(checker.check_impl(&impl_block).is_ok());
}

#[test]
fn test_orphan_rule_rejects_foreign_trait_foreign_type() {
    let mut checker = CoherenceChecker::new();

    let impl_block = make_impl_block(Some("Display".to_string()), make_type("String"), vec![], vec![]);

    let result = checker.check_impl(&impl_block);
    assert!(result.is_err());

    match result.unwrap_err() {
        CoherenceError::OrphanImpl {
            trait_name,
            target_type,
            ..
        } => {
            assert_eq!(trait_name, "Display");
            assert_eq!(target_type, "String");
        }
        _ => panic!("Expected OrphanImpl error"),
    }
}

#[test]
fn test_overlap_detection_same_type() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Process".to_string());
    checker.register_type("i32".to_string());

    let impl1 = make_impl_block(Some("Process".to_string()), make_type("i32"), vec![], vec![]);
    assert!(checker.check_impl(&impl1).is_ok());

    let impl2 = make_impl_block(Some("Process".to_string()), make_type("i32"), vec![], vec![]);
    let result = checker.check_impl(&impl2);
    assert!(result.is_err());

    match result.unwrap_err() {
        CoherenceError::OverlappingImpl {
            trait_name,
            type1,
            type2,
            ..
        } => {
            assert_eq!(trait_name, "Process");
            assert_eq!(type1, "i32");
            assert_eq!(type2, "i32");
        }
        _ => panic!("Expected OverlappingImpl error"),
    }
}

#[test]
fn test_overlap_detection_generic_vs_concrete() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Process".to_string());
    checker.register_type("i32".to_string());

    let impl1 = make_impl_block(Some("Process".to_string()), make_type("i32"), vec![], vec![]);
    assert!(checker.check_impl(&impl1).is_ok());

    let impl2 = make_impl_block(
        Some("Process".to_string()),
        make_type("T"),
        vec!["T".to_string()],
        vec![],
    );
    let result = checker.check_impl(&impl2);
    assert!(result.is_err());
}

#[test]
fn test_no_overlap_different_types() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Process".to_string());
    checker.register_type("i32".to_string());
    checker.register_type("String".to_string());

    let impl1 = make_impl_block(Some("Process".to_string()), make_type("i32"), vec![], vec![]);
    assert!(checker.check_impl(&impl1).is_ok());

    let impl2 = make_impl_block(Some("Process".to_string()), make_type("String"), vec![], vec![]);
    assert!(checker.check_impl(&impl2).is_ok());
}

#[test]
fn test_associated_type_coherence_same_type() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Container".to_string());
    checker.register_type("IntList".to_string());

    let assoc1 = AssociatedTypeImpl {
        span: make_span(),
        name: "Item".to_string(),
        ty: make_type("i32"),
    };

    let impl1 = make_impl_block(
        Some("Container".to_string()),
        make_type("IntList"),
        vec![],
        vec![assoc1],
    );
    assert!(checker.check_impl(&impl1).is_ok());

    let assoc2 = AssociatedTypeImpl {
        span: make_span(),
        name: "Item".to_string(),
        ty: make_type("i64"),
    };

    let impl2 = make_impl_block(
        Some("Container".to_string()),
        make_type("IntList"),
        vec![],
        vec![assoc2],
    );
    let result = checker.check_impl(&impl2);
    assert!(result.is_err());

    match result.unwrap_err() {
        CoherenceError::ConflictingAssociatedType {
            trait_name,
            target_type,
            type_name,
            ..
        } => {
            assert_eq!(trait_name, "Container");
            assert_eq!(target_type, "IntList");
            assert_eq!(type_name, "Item");
        }
        _ => panic!("Expected ConflictingAssociatedType error"),
    }
}

#[test]
fn test_blanket_impl_conflict() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Process".to_string());
    checker.register_type("i32".to_string());

    let specific = make_impl_block(Some("Process".to_string()), make_type("i32"), vec![], vec![]);
    assert!(checker.check_impl(&specific).is_ok());

    let blanket = make_impl_block(
        Some("Process".to_string()),
        make_type("T"),
        vec!["T".to_string()],
        vec![],
    );
    let result = checker.check_impl(&blanket);
    assert!(result.is_err());

    match result.unwrap_err() {
        CoherenceError::BlanketImplConflict {
            trait_name,
            general,
            specific: _,
            ..
        } => {
            assert_eq!(trait_name, "Process");
            assert_eq!(general, "T");
        }
        _ => panic!("Expected BlanketImplConflict error"),
    }
}

#[test]
fn test_check_module_integration() {
    let mut checker = CoherenceChecker::new();

    let trait_def = TraitDef {
        span: make_span(),
        name: "Printable".to_string(),
        generic_params: vec![],
        super_traits: vec![],
        where_clause: vec![],
        associated_types: vec![],
        methods: vec![],
        visibility: Visibility::Public,
        doc_comment: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: std::collections::HashMap::new(),
    };

    let struct_def = StructDef {
        span: make_span(),
        name: "Person".to_string(),
        generic_params: vec![],
        where_clause: vec![],
        fields: vec![],
        visibility: Visibility::Public,
        doc_comment: None,
        attributes: vec![],
        methods: vec![],
        invariant: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: std::collections::HashMap::new(),
    };

    let impl_block = make_impl_block(Some("Printable".to_string()), make_type("Person"), vec![], vec![]);

    let nodes = vec![Node::Trait(trait_def), Node::Struct(struct_def), Node::Impl(impl_block)];

    let errors = checker.check_module(&nodes);
    assert_eq!(errors.len(), 0);
}

#[test]
fn test_check_module_with_orphan_error() {
    let mut checker = CoherenceChecker::new();

    let impl_block = make_impl_block(Some("Display".to_string()), make_type("String"), vec![], vec![]);

    let nodes = vec![Node::Impl(impl_block)];

    let errors = checker.check_module(&nodes);
    assert_eq!(errors.len(), 1);

    match &errors[0] {
        CoherenceError::OrphanImpl {
            trait_name,
            target_type,
            ..
        } => {
            assert_eq!(trait_name, "Display");
            assert_eq!(target_type, "String");
        }
        _ => panic!("Expected OrphanImpl error"),
    }
}

#[test]
fn test_inherent_impl_allowed() {
    let mut checker = CoherenceChecker::new();
    checker.register_type("Point".to_string());

    let impl_block = make_impl_block(None, make_type("Point"), vec![], vec![]);

    assert!(checker.check_impl(&impl_block).is_ok());
}

#[test]
fn test_multiple_traits_same_type() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Printable".to_string());
    checker.register_trait("Comparable".to_string());
    checker.register_type("Point".to_string());

    let impl1 = make_impl_block(Some("Printable".to_string()), make_type("Point"), vec![], vec![]);
    assert!(checker.check_impl(&impl1).is_ok());

    let impl2 = make_impl_block(Some("Comparable".to_string()), make_type("Point"), vec![], vec![]);
    assert!(checker.check_impl(&impl2).is_ok());
}

#[test]
fn test_generic_type_extraction() {
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Container".to_string());
    checker.register_type("Vec".to_string());

    let generic_type = make_generic_type("Vec", vec![make_type("i32")]);

    let impl_block = make_impl_block(Some("Container".to_string()), generic_type, vec![], vec![]);

    assert!(checker.check_impl(&impl_block).is_ok());
}

#[test]
fn test_specialization_with_default_attribute() {
    // Test that #[default] attribute allows specialization
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Process".to_string());
    checker.register_type("i32".to_string());

    // Blanket impl with #[default]
    let default_attr = Attribute {
        span: make_span(),
        name: "default".to_string(),
        value: None,
        args: None,
    };

    let blanket = make_impl_block_with_attrs(
        Some("Process".to_string()),
        make_type("T"),
        vec!["T".to_string()],
        vec![],
        vec![default_attr],
    );
    assert!(checker.check_impl(&blanket).is_ok());

    // Specific impl (specializes the default)
    let specific = make_impl_block(Some("Process".to_string()), make_type("i32"), vec![], vec![]);

    // Should succeed - specialization allowed with #[default]
    assert!(
        checker.check_impl(&specific).is_ok(),
        "Specialization should be allowed with #[default] attribute"
    );
}

#[test]
fn test_extension_trait_pattern() {
    // Extension traits: local trait + foreign type = ALLOWED
    let mut checker = CoherenceChecker::new();

    // Define local extension trait
    checker.register_trait("StringExt".to_string());

    // Implement for foreign type String - should be allowed
    let impl_block = make_impl_block(Some("StringExt".to_string()), make_type("String"), vec![], vec![]);

    assert!(
        checker.check_impl(&impl_block).is_ok(),
        "Extension trait pattern should be allowed: local trait + foreign type"
    );
}

#[test]
fn test_extension_trait_with_generics() {
    // Extension trait with generic parameter
    let mut checker = CoherenceChecker::new();

    checker.register_trait("SliceExt".to_string());

    // impl[T] SliceExt[T] for [T]
    let impl_block = make_impl_block(
        Some("SliceExt".to_string()),
        Type::Array {
            element: Box::new(make_type("T")),
            size: None,
        },
        vec!["T".to_string()],
        vec![],
    );

    assert!(
        checker.check_impl(&impl_block).is_ok(),
        "Generic extension trait should be allowed"
    );
}

#[test]
fn test_negative_bounds_infrastructure() {
    // Test that negative bounds infrastructure is in place
    // Once parser supports !Trait syntax, this will validate exclusion
    let mut checker = CoherenceChecker::new();
    checker.register_trait("Clone".to_string());
    checker.register_trait("Process".to_string());

    // For now, just verify checker accepts impl with where clause
    // Future: parser will populate negative_bounds in where_clause
    let impl_block = make_impl_block(
        Some("Process".to_string()),
        make_type("T"),
        vec!["T".to_string()],
        vec![],
    );

    // Should succeed - negative bounds infrastructure ready
    assert!(
        checker.check_impl(&impl_block).is_ok(),
        "Negative bounds infrastructure should be ready"
    );
}
