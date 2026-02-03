//! Type system tests for mixins (Feature #2200, #2201)

use simple_parser::{Parser, Node};
use simple_type::{check, Type, TypeChecker};

#[test]
fn test_register_simple_mixin() {
    // Test registering a simple mixin with fields
    let source = r#"
mixin Timestamped:
    created_at: i64
    updated_at: i64
"#;

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("Parse should succeed");
    
    // Type check should not error
    let result = check(&module.items);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result);
    
    // Verify mixin was registered
    let mut tc = TypeChecker::new();
    for item in &module.items {
        if let Node::Mixin(mixin) = item {
            // Mixin should be in environment
            assert_eq!(mixin.name, "Timestamped");
            assert_eq!(mixin.fields.len(), 2);
        }
    }
}

#[test]
fn test_register_generic_mixin() {
    // Test registering a generic mixin
    let source = r#"
mixin Container[T]:
    items: [T]
"#;

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("Parse should succeed");
    
    let result = check(&module.items);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result);
}

#[test]
fn test_register_mixin_with_methods() {
    // Test registering a mixin with methods
    let source = r#"
mixin Printable:
    fn to_string() -> str:
        return "test"
"#;

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("Parse should succeed");
    
    let result = check(&module.items);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result);
}

//==============================================================================
// Step 2: Type Substitution Tests (Feature #2201)
//==============================================================================

#[test]
fn test_substitute_simple_type_param() {
    // Test: Substitute simple type param T -> i64
    use simple_type::{Type, MixinInfo};
    use std::collections::HashMap;
    
    let mixin = MixinInfo {
        name: "Container".to_string(),
        type_params: vec!["T".to_string()],
        fields: vec![("value".to_string(), Type::TypeParam("T".to_string()))],
        methods: vec![],
        required_traits: vec![],
        required_methods: vec![],
    };
    
    let instantiated = mixin.instantiate(&[Type::Int])
        .expect("Instantiation should succeed");
    
    assert_eq!(instantiated.type_params.len(), 0);
    assert_eq!(instantiated.fields.len(), 1);
    assert_eq!(instantiated.fields[0].0, "value");
    assert_eq!(instantiated.fields[0].1, Type::Int);
}

#[test]
fn test_substitute_nested_generic() {
    // Test: Substitute nested generic [T] -> [i64]
    use simple_type::{Type, MixinInfo};
    
    let mixin = MixinInfo {
        name: "Container".to_string(),
        type_params: vec!["T".to_string()],
        fields: vec![
            ("items".to_string(), Type::Array(Box::new(Type::TypeParam("T".to_string()))))
        ],
        methods: vec![],
        required_traits: vec![],
        required_methods: vec![],
    };
    
    let instantiated = mixin.instantiate(&[Type::Int])
        .expect("Instantiation should succeed");
    
    assert_eq!(instantiated.fields[0].1, Type::Array(Box::new(Type::Int)));
}

#[test]
fn test_substitute_in_function_type() {
    // Test: Substitute type param in function signature
    use simple_type::{Type, MixinInfo, FunctionType};
    
    let mixin = MixinInfo {
        name: "Processor".to_string(),
        type_params: vec!["T".to_string()],
        fields: vec![],
        methods: vec![
            ("process".to_string(), FunctionType {
                params: vec![Type::TypeParam("T".to_string())],
                ret: Type::TypeParam("T".to_string()),
            })
        ],
        required_traits: vec![],
        required_methods: vec![],
    };
    
    let instantiated = mixin.instantiate(&[Type::Str])
        .expect("Instantiation should succeed");
    
    assert_eq!(instantiated.methods[0].1.params[0], Type::Str);
    assert_eq!(instantiated.methods[0].1.ret, Type::Str);
}

#[test]
fn test_instantiate_multi_param_generic() {
    // Test: Instantiate mixin with multiple type parameters
    use simple_type::{Type, MixinInfo};
    
    let mixin = MixinInfo {
        name: "KeyValue".to_string(),
        type_params: vec!["K".to_string(), "V".to_string()],
        fields: vec![
            ("key".to_string(), Type::TypeParam("K".to_string())),
            ("value".to_string(), Type::TypeParam("V".to_string())),
        ],
        methods: vec![],
        required_traits: vec![],
        required_methods: vec![],
    };
    
    let instantiated = mixin.instantiate(&[Type::Str, Type::Int])
        .expect("Instantiation should succeed");
    
    assert_eq!(instantiated.fields[0].1, Type::Str);
    assert_eq!(instantiated.fields[1].1, Type::Int);
}

#[test]
fn test_wrong_type_arg_count() {
    // Test: Wrong number of type arguments should error
    use simple_type::{Type, MixinInfo};
    
    let mixin = MixinInfo {
        name: "Container".to_string(),
        type_params: vec!["T".to_string()],
        fields: vec![],
        methods: vec![],
        required_traits: vec![],
        required_methods: vec![],
    };
    
    // Try with 0 args (should fail)
    let result = mixin.instantiate(&[]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("expects 1 type arguments, got 0"));
    
    // Try with 2 args (should fail)
    let result = mixin.instantiate(&[Type::Int, Type::Str]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("expects 1 type arguments, got 2"));
}

//==============================================================================
// Step 3: Composition Registration Tests (Feature #2201)
//==============================================================================

#[test]
fn test_apply_simple_mixin() {
    // Test: Class applying a simple mixin
    let source = r#"
mixin Timestamped:
    created_at: i64
    updated_at: i64

class User:
    mixin Timestamped
    name: str
"#;

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("Parse should succeed");
    
    let result = check(&module.items);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result);
}

#[test]
fn test_apply_generic_mixin() {
    // Test: Class applying a generic mixin with type args
    let source = r#"
mixin Container[T]:
    items: [T]

class UserList:
    mixin Container[str]
    count: i32
"#;

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("Parse should succeed");
    
    let result = check(&module.items);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result);
}
