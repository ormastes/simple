// ============================================================================
// LL(1) Parser Integration Tests
// ============================================================================

#[test]
fn ll1_parser_registers_macro_definitions() {
    use simple_parser::Parser;

    let code = r#"
macro my_macro(x: Int) -> (returns result: Int):
    emit result:
        x + 1
"#;

    let mut parser = Parser::new(code);
    let _module = parser.parse().unwrap();

    // Check that the macro is registered in the registry
    assert!(parser.macro_registry().has_macro("my_macro"));
}

#[test]
fn ll1_parser_with_ll1_mode_enabled() {
    use simple_parser::Parser;

    let code = r#"
macro add_one(x: Int) -> (returns result: Int):
    emit result:
        x + 1
"#;

    let mut parser = Parser::with_ll1_macros(code);
    assert!(parser.macro_registry().is_ll1_mode());
    let _module = parser.parse().unwrap();

    // Macro should be registered
    assert!(parser.macro_registry().has_macro("add_one"));
}

#[test]
fn ll1_parser_registers_multiple_macros() {
    use simple_parser::Parser;

    let code = r#"
macro first(x: Int) -> (returns result: Int):
    emit result:
        x

macro second(x: Int) -> (returns result: Int):
    emit result:
        x * 2

macro third(x: Int) -> (returns result: Int):
    emit result:
        x * 3
"#;

    let mut parser = Parser::new(code);
    let _module = parser.parse().unwrap();

    // All three macros should be registered
    assert!(parser.macro_registry().has_macro("first"));
    assert!(parser.macro_registry().has_macro("second"));
    assert!(parser.macro_registry().has_macro("third"));
}

#[test]
fn ll1_parser_macro_registry_const_eval() {
    use simple_parser::macro_registry::{ConstEvalContext, ConstValue, MacroRegistry};

    let registry = MacroRegistry::new();
    let mut ctx = ConstEvalContext::default();
    ctx.bindings.insert("x".to_string(), ConstValue::Int(10));
    ctx.bindings.insert("name".to_string(), ConstValue::Str("foo".to_string()));

    // Test template substitution
    let result = registry.substitute_templates("get_{name}_{x}", &ctx);
    assert_eq!(result, "get_foo_10");
}

#[test]
fn ll1_parser_macro_registry_template_with_quotes() {
    use simple_parser::macro_registry::{ConstEvalContext, ConstValue, MacroRegistry};

    let registry = MacroRegistry::new();
    let mut ctx = ConstEvalContext::default();
    ctx.bindings.insert("i".to_string(), ConstValue::Int(0));

    // Test quote stripping
    let result = registry.substitute_templates("\"axis{i}\"", &ctx);
    assert_eq!(result, "axis0");
}
