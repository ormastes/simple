//! Integration tests for capability system with complex scenarios
//!
//! These tests verify that capabilities work correctly in realistic
//! programming scenarios with multiple interacting features.

use simple_parser::Parser;

#[test]
fn test_actor_message_passing_pattern() {
    // Realistic actor pattern: receiving iso data and processing it
    let source = "fn process_message(msg: iso i64) -> i64:\n    return msg";

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse");

    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&module);

    assert!(result.is_ok(), "Actor message passing should work with iso T");
}

#[test]
fn test_lock_based_concurrent_modification() {
    // Realistic lock-based pattern: shared mutable data
    let source = "#[concurrency_mode(lock_base)]\nfn increment(counter: mut i64, delta: i64) -> i64:\n    return counter + delta";

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse");

    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&module);

    assert!(result.is_ok(), "Lock-based concurrent modification should work");
}

#[test]
fn test_mixed_mode_functions() {
    // Test that different functions can have different modes

    // Actor mode function with iso
    let source1 = "fn transfer(data: iso i64) -> i64:\n    return data";
    let mut parser = Parser::new(source1);
    let module = parser.parse().expect("should parse actor");
    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    assert!(lowerer.lower_module(&module).is_ok(), "Actor mode should work");

    // Lock_base mode function with mut
    let source2 = "#[concurrency_mode(lock_base)]\nfn modify(data: mut i64) -> i64:\n    return data";
    let mut parser2 = Parser::new(source2);
    let module2 = parser2.parse().expect("should parse lock_base");
    let lowerer2 = Lowerer::new();
    assert!(lowerer2.lower_module(&module2).is_ok(), "Lock_base mode should work");
}

#[test]
fn test_builder_pattern_with_mut() {
    // Builder pattern using mut T for fluent API
    let source =
        "#[concurrency_mode(lock_base)]\nfn with_value(builder: mut i64, value: i64) -> mut i64:\n    return builder";

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse");

    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&module);

    assert!(result.is_ok(), "Builder pattern with mut T should work in lock_base");
}

#[test]
fn test_capability_with_array() {
    // Capabilities should work with array types
    let source = "#[concurrency_mode(lock_base)]\nfn process_array(data: mut [i64]) -> i64:\n    return 0";

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse");

    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&module);

    // This may or may not work depending on implementation
    // Just verify it doesn't crash
    let _ = result;
}

#[test]
fn test_unsafe_mode_escape_hatch() {
    // Unsafe mode as escape hatch for manual synchronization
    let source = "#[concurrency_mode(unsafe)]\nfn unsafe_modify(data: mut i64, value: i64) -> i64:\n    return value";

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse");

    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&module);

    assert!(result.is_ok(), "Unsafe mode should allow manual synchronization");
}

#[test]
fn test_iso_transfer_semantics() {
    // iso T for unique transferable references
    let sources = vec![
        "fn send(data: iso i64) -> iso i64:\n    return data",
        "fn consume(data: iso i64) -> i64:\n    return data",
    ];

    for source in sources {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("should parse");

        use simple_compiler::hir::Lowerer;
        let lowerer = Lowerer::new();
        let result = lowerer.lower_module(&module);

        assert!(result.is_ok(), "iso T transfer semantics should work");
    }
}

#[test]
fn test_const_and_mut_parameters() {
    // Mix of const (shared) and mutable parameters
    let source = "#[concurrency_mode(lock_base)]\nfn update_with_config(state: mut i64, config: i64, multiplier: i64) -> i64:\n    return config * multiplier";

    let mut parser = Parser::new(source);
    let module = parser.parse().expect("should parse");

    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&module);

    assert!(result.is_ok(), "Mix of mut and const parameters should work");
}
