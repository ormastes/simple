//! Tests for decorator helper methods on FunctionDef
//! Tests @property_test, @snapshot_test, and @test decorators

use simple_parser::{Parser, Module, Node, Expr};

#[test]
fn test_property_test_decorator() {
    let input = r#"
@property_test
fn test_sort(arr: [i64]):
    let sorted = sort(arr)
    expect(sorted).to_be_sorted()
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_property_test(), "Should be property test");
        assert!(func.is_test(), "Should be a test");
        assert!(!func.is_snapshot_test(), "Should not be snapshot test");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_property_test_with_params() {
    let input = r#"
@property_test(iterations: 1000, seed: 42)
fn test_commutative(a: i64, b: i64):
    expect(add(a, b)).to_equal(add(b, a))
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_property_test());
        
        let config = func.property_test_config();
        assert!(config.is_some(), "Should have config parameters");
        
        let args = config.unwrap();
        assert_eq!(args.len(), 2);
        
        // Check for named arguments
        assert!(args.iter().any(|arg| arg.name.as_ref().map_or(false, |n| n == "iterations")));
        assert!(args.iter().any(|arg| arg.name.as_ref().map_or(false, |n| n == "seed")));
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_snapshot_test_decorator() {
    let input = r#"
@snapshot_test
fn test_render_output():
    let result = render_template("user", data)
    expect_snapshot(result)
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_snapshot_test(), "Should be snapshot test");
        assert!(func.is_test(), "Should be a test");
        assert!(!func.is_property_test(), "Should not be property test");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_snapshot_test_with_format() {
    let input = r#"
@snapshot_test(format: "json", name: "api_response")
fn test_api_output():
    let response = api.get_user(42)
    expect_snapshot(response)
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_snapshot_test());
        
        let config = func.snapshot_test_config();
        assert!(config.is_some(), "Should have config parameters");
        
        let args = config.unwrap();
        assert_eq!(args.len(), 2);
        
        // Check for named arguments
        assert!(args.iter().any(|arg| arg.name.as_ref().map_or(false, |n| n == "format")));
        assert!(args.iter().any(|arg| arg.name.as_ref().map_or(false, |n| n == "name")));
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_regular_test_decorator() {
    let input = r#"
@test
fn test_addition():
    expect(add(2, 2)).to_equal(4)
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_test(), "Should be a test");
        assert!(!func.is_property_test(), "Should not be property test");
        assert!(!func.is_snapshot_test(), "Should not be snapshot test");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_multiple_decorators() {
    let input = r#"
@property_test(iterations: 500)
@slow
fn test_expensive_property(x: i64):
    expect(expensive_computation(x)).to_be_positive()
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_property_test());
        assert_eq!(func.decorators.len(), 2);
        
        // Check both decorators exist
        let has_property = func.decorators.iter().any(|d| {
            matches!(&d.name, Expr::Identifier(n) if n == "property_test")
        });
        let has_slow = func.decorators.iter().any(|d| {
            matches!(&d.name, Expr::Identifier(n) if n == "slow")
        });
        
        assert!(has_property, "Should have @property_test");
        assert!(has_slow, "Should have @slow");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_no_test_decorator() {
    let input = r#"
fn regular_function(x: i64) -> i64:
    return x * 2
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 1);
    
    if let Node::Function(func) = &module.items[0] {
        assert!(!func.is_test(), "Should not be a test");
        assert!(!func.is_property_test(), "Should not be property test");
        assert!(!func.is_snapshot_test(), "Should not be snapshot test");
        assert!(func.property_test_config().is_none());
        assert!(func.snapshot_test_config().is_none());
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_property_test_no_params() {
    let input = r#"
@property_test
fn test_idempotent(x: String):
    expect(normalize(normalize(x))).to_equal(normalize(x))
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_property_test());
        assert!(func.property_test_config().is_none(), "Should have no config params");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_snapshot_test_multiple_formats() {
    let input = r#"
@snapshot_test(format: "yaml")
fn test_config_yaml():
    expect_snapshot(config)

@snapshot_test(format: "json")
fn test_config_json():
    expect_snapshot(config)

@snapshot_test(format: "text")
fn test_config_text():
    expect_snapshot(config)
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    assert_eq!(module.items.len(), 3);
    
    // All should be snapshot tests
    for item in &module.items {
        if let Node::Function(func) = item {
            assert!(func.is_snapshot_test());
            assert!(func.is_test());
        }
    }
}

#[test]
fn test_combined_with_effects() {
    let input = r#"
@property_test
@io
fn test_with_io(path: String):
    let content = read_file(path)
    expect(content.len()).to_be_positive()
"#;
    
    let mut parser = Parser::new(input);
    let result: Result<Module, _> = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    
    let module = result.unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_property_test(), "Should be property test");
        assert!(func.has_io(), "Should have @io effect");
        assert_eq!(func.decorators.len(), 1); // Only @property_test (not @io)
        assert_eq!(func.effects.len(), 1); // @io is an effect
    } else {
        panic!("Expected function");
    }
}
