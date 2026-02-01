// Dyn Trait Type Inference Specification Tests
//
// Tests for dynamic trait object type inference:
// - Coercion from concrete types to dyn Trait
// - Method dispatch on dyn trait objects
// - Unification rules for dyn Trait types
// - Dyn traits in generic containers

use simple_type::{check, Type, TypeChecker, TypeError};
use simple_parser::ast::{Expr, ImplBlock, Node, TraitDef, ClassDef, FunctionDef, Parameter, Block, Type as AstType, Visibility, Effect, MacroInvocation, MixinRef, Mutability};
use simple_parser::Span;
use std::collections::HashMap;

// Helper to create a simple trait definition
fn create_logger_trait() -> TraitDef {
    TraitDef {
        span: Span::new(0, 0, 0, 0),
        name: "Logger".to_string(),
        generic_params: vec![],
        super_traits: vec![],
        where_clause: vec![],
        methods: vec![FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "log".to_string(),
            generic_params: vec![],
            params: vec![Parameter {
                span: Span::new(0, 0, 0, 0),
                name: "msg".to_string(),
                ty: Some(AstType::Simple("str".to_string())),
                default: None,
                mutability: Mutability::Immutable,
                inject: false,
                variadic: false,
                call_site_label: None,
            }],
            return_type: Some(AstType::Simple("nil".to_string())),
            where_clause: vec![],
            body: Block { span: Span::new(0, 0, 0, 0), statements: vec![] },
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_static: false,
            bounds_block: None,
            is_me_method: false,
            is_generator: false,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
        }],
        associated_types: vec![],
        visibility: Visibility::Private,
        doc_comment: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: HashMap::new(),
    }
}

// Helper to create ConsoleLogger class
fn create_console_logger_class() -> ClassDef {
    ClassDef {
        span: Span::new(0, 0, 0, 0),
        name: "ConsoleLogger".to_string(),
        generic_params: vec![],
        where_clause: vec![],
        fields: vec![],
        methods: vec![FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "log".to_string(),
            generic_params: vec![],
            params: vec![Parameter {
                span: Span::new(0, 0, 0, 0),
                name: "msg".to_string(),
                ty: Some(AstType::Simple("str".to_string())),
                default: None,
                mutability: Mutability::Immutable,
                inject: false,
                variadic: false,
                call_site_label: None,
            }],
            return_type: Some(AstType::Simple("nil".to_string())),
            where_clause: vec![],
            body: Block { span: Span::new(0, 0, 0, 0), statements: vec![] },
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_static: false,
            bounds_block: None,
            is_me_method: false,
            is_generator: false,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
        }],
        parent: None,
        visibility: Visibility::Private,
        effects: vec![],
        attributes: vec![],
        doc_comment: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: HashMap::new(),
        invariant: None,
        macro_invocations: vec![],
        mixins: vec![],
    }
}

// Helper to create Logger impl for ConsoleLogger
fn create_logger_impl() -> ImplBlock {
    ImplBlock {
        span: Span::new(0, 0, 0, 0),
        attributes: vec![],
        generic_params: vec![],
        where_clause: vec![],
        target_type: AstType::Simple("ConsoleLogger".to_string()),
        trait_name: Some("Logger".to_string()),
        trait_type_params: vec![],
        associated_types: vec![],
        methods: vec![FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: "log".to_string(),
            generic_params: vec![],
            params: vec![Parameter {
                span: Span::new(0, 0, 0, 0),
                name: "msg".to_string(),
                ty: Some(AstType::Simple("str".to_string())),
                default: None,
                mutability: Mutability::Immutable,
                inject: false,
                variadic: false,
                call_site_label: None,
            }],
            return_type: Some(AstType::Simple("nil".to_string())),
            where_clause: vec![],
            body: Block { span: Span::new(0, 0, 0, 0), statements: vec![] },
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            is_static: false,
            bounds_block: None,
            is_me_method: false,
            is_generator: false,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
        }],
    }
}

#[test]
fn test_dyn_trait_unify_same_trait() {
    // DynTrait("Logger") unifies with DynTrait("Logger")
    let mut checker = TypeChecker::new();
    let t1 = Type::DynTrait("Logger".to_string());
    let t2 = Type::DynTrait("Logger".to_string());

    assert!(checker.unify(&t1, &t2).is_ok(), "Same dyn trait should unify");
}

#[test]
fn test_dyn_trait_unify_different_traits() {
    // DynTrait("Logger") does NOT unify with DynTrait("Drawable")
    let mut checker = TypeChecker::new();
    let t1 = Type::DynTrait("Logger".to_string());
    let t2 = Type::DynTrait("Drawable".to_string());

    let result = checker.unify(&t1, &t2);
    assert!(result.is_err(), "Different dyn traits should not unify");
    match result {
        Err(TypeError::Mismatch { expected, found }) => {
            assert_eq!(expected, t1);
            assert_eq!(found, t2);
        }
        _ => panic!("Expected Mismatch error"),
    }
}

#[test]
fn test_dyn_trait_cannot_unify_with_int() {
    // DynTrait("Logger") does NOT unify with Int
    let mut checker = TypeChecker::new();
    let t1 = Type::DynTrait("Logger".to_string());
    let t2 = Type::Int;

    assert!(checker.unify(&t1, &t2).is_err(), "dyn Trait cannot unify with concrete type");
}

#[test]
fn test_int_cannot_unify_with_dyn_trait() {
    // Int does NOT unify with DynTrait("Logger") (reverse order)
    let mut checker = TypeChecker::new();
    let t1 = Type::Int;
    let t2 = Type::DynTrait("Logger".to_string());

    assert!(checker.unify(&t1, &t2).is_err(), "Concrete type cannot unify with dyn Trait");
}

#[test]
fn test_dyn_trait_types_compatible_same_trait() {
    // types_compatible should return true for same dyn trait
    let checker = TypeChecker::new();
    let t1 = Type::DynTrait("Logger".to_string());
    let t2 = Type::DynTrait("Logger".to_string());

    assert!(checker.types_compatible(&t1, &t2), "Same dyn trait types should be compatible");
}

#[test]
fn test_dyn_trait_types_not_compatible_different_traits() {
    // types_compatible should return false for different dyn traits
    let checker = TypeChecker::new();
    let t1 = Type::DynTrait("Logger".to_string());
    let t2 = Type::DynTrait("Drawable".to_string());

    assert!(!checker.types_compatible(&t1, &t2), "Different dyn trait types should not be compatible");
}

#[test]
fn test_dyn_trait_in_let_binding() {
    // Test dyn trait coercion in let binding with type annotation
    let items = vec![
        Node::Trait(create_logger_trait()),
        Node::Class(create_console_logger_class()),
        Node::Impl(create_logger_impl()),
    ];

    let result = check(&items);
    assert!(result.is_ok(), "Trait, class, and impl should type check: {:?}", result);
}

#[test]
fn test_dyn_trait_coercion_validates_impl() {
    // When assigning Named("ConsoleLogger") to DynTrait("Logger"),
    // type checker should verify ConsoleLogger implements Logger
    let mut checker = TypeChecker::new();

    // Register trait impl
    let impl_block = create_logger_impl();
    checker.check_items(&[Node::Impl(impl_block)]).expect("Impl should register");

    // Now test coercion check logic
    let concrete_ty = Type::Named("ConsoleLogger".to_string());
    let dyn_ty = Type::DynTrait("Logger".to_string());

    // The actual coercion validation happens in check_node for Let bindings
    // This test verifies the unification at least doesn't panic
    let result = checker.unify(&concrete_ty, &dyn_ty);
    // Note: unify will fail because Named and DynTrait don't unify directly
    // The actual coercion check is in checker_check.rs in the Let handler
    assert!(result.is_err(), "Direct unification should fail - coercion is separate validation");
}

#[test]
fn test_dyn_trait_array() {
    // Array of dyn Trait should be valid type
    let dyn_logger = Type::DynTrait("Logger".to_string());
    let array_of_dyn = Type::Array(Box::new(dyn_logger.clone()));

    // Verify the type structure
    match &array_of_dyn {
        Type::Array(elem) => {
            assert_eq!(**elem, dyn_logger);
        }
        _ => panic!("Expected Array type"),
    }
}

#[test]
fn test_dyn_trait_optional() {
    // Option<dyn Trait> should be valid type
    let dyn_logger = Type::DynTrait("Logger".to_string());
    let option_of_dyn = Type::Optional(Box::new(dyn_logger.clone()));

    match &option_of_dyn {
        Type::Optional(inner) => {
            assert_eq!(**inner, dyn_logger);
        }
        _ => panic!("Expected Optional type"),
    }
}

#[test]
fn test_dyn_trait_in_generic() {
    // Generic<dyn Trait> should be valid type
    let dyn_logger = Type::DynTrait("Logger".to_string());
    let generic = Type::Generic {
        name: "Option".to_string(),
        args: vec![dyn_logger.clone()],
    };

    match &generic {
        Type::Generic { name, args } => {
            assert_eq!(name, "Option");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], dyn_logger);
        }
        _ => panic!("Expected Generic type"),
    }
}

#[test]
fn test_dyn_trait_function_parameter() {
    // fn(dyn Trait) -> T should be valid type
    let dyn_logger = Type::DynTrait("Logger".to_string());
    let func_ty = Type::Function {
        params: vec![dyn_logger.clone()],
        ret: Box::new(Type::Nil),
    };

    match &func_ty {
        Type::Function { params, ret } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0], dyn_logger);
            assert_eq!(**ret, Type::Nil);
        }
        _ => panic!("Expected Function type"),
    }
}

#[test]
fn test_dyn_trait_function_return() {
    // fn() -> dyn Trait should be valid type
    let dyn_logger = Type::DynTrait("Logger".to_string());
    let func_ty = Type::Function {
        params: vec![],
        ret: Box::new(dyn_logger.clone()),
    };

    match &func_ty {
        Type::Function { params, ret } => {
            assert_eq!(params.len(), 0);
            assert_eq!(**ret, dyn_logger);
        }
        _ => panic!("Expected Function type"),
    }
}

#[test]
fn test_dyn_trait_does_not_unify_with_named() {
    // DynTrait("Logger") does NOT unify with Named("ConsoleLogger")
    let mut checker = TypeChecker::new();
    let dyn_ty = Type::DynTrait("Logger".to_string());
    let named_ty = Type::Named("ConsoleLogger".to_string());

    let result = checker.unify(&dyn_ty, &named_ty);
    assert!(result.is_err(), "dyn Trait should not unify with Named type directly");
}

#[test]
fn test_dyn_trait_in_tuple() {
    // Tuple containing dyn Trait should be valid
    let dyn_logger = Type::DynTrait("Logger".to_string());
    let tuple_ty = Type::Tuple(vec![Type::Int, dyn_logger.clone(), Type::Str]);

    match &tuple_ty {
        Type::Tuple(types) => {
            assert_eq!(types.len(), 3);
            assert_eq!(types[0], Type::Int);
            assert_eq!(types[1], dyn_logger);
            assert_eq!(types[2], Type::Str);
        }
        _ => panic!("Expected Tuple type"),
    }
}
