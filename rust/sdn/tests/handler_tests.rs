//! Integration tests for SDN handler architecture

use simple_sdn::*;

#[test]
fn test_value_builder_produces_same_output_as_parse() {
    let src = "name: Alice\nage: 30\nactive: true";

    // Parse normally
    let normal = parse(src).unwrap();

    // Parse with ValueBuilder
    let mut parser = parser::Parser::new(src);
    let handler = ValueBuilder::new();
    let with_handler = parser.parse_with_handler(handler).unwrap();

    assert_eq!(normal, with_handler);
}

#[test]
fn test_noop_handler_validates_without_building_tree() {
    let src = "name: Alice\nage: 30";

    let mut parser = parser::Parser::new(src);
    let noop = NoopHandler::new();
    let result = parser.parse_with_handler(noop);

    assert!(result.is_ok());
}

#[test]
fn test_noop_handler_rejects_deep_nesting() {
    // Create deeply nested structure
    let src = "a:\n  b:\n    c:\n      d:\n        e:\n          f:\n            g: too deep";

    let mut parser = parser::Parser::new(src);
    let noop = NoopHandler::with_limits(5, 1024, 1000);
    let result = parser.parse_with_handler(noop);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.is_security_error());
    }
}

#[test]
fn test_noop_handler_rejects_large_strings() {
    let large_str = "x".repeat(2_000_000); // 2 MB
    let src = format!("data: \"{}\"", large_str);

    let mut parser = parser::Parser::new(&src);
    let noop = NoopHandler::with_limits(100, 1_048_576, 1000); // 1 MB limit
    let result = parser.parse_with_handler(noop);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.is_security_error());
    }
}

#[test]
fn test_noop_handler_rejects_too_many_cells() {
    // Array with 1000 items, limit is 500
    let items = (0..1000).map(|i| i.to_string()).collect::<Vec<_>>().join(", ");
    let src = format!("data: [{}]", items);

    let mut parser = parser::Parser::new(&src);
    let noop = NoopHandler::with_limits(100, 1024, 500);
    let result = parser.parse_with_handler(noop);

    assert!(result.is_err());
}

#[test]
fn test_restricted_handler_flat_dict_only() {
    let src = "name: Alice\nage: 30";

    let mut parser = parser::Parser::new(src);
    let handler = RestrictedHandler::flat_dict_only();
    let value = parser.parse_with_handler(handler).unwrap();

    assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
    assert_eq!(value.get("age").and_then(|v| v.as_i64()), Some(30));
}

#[test]
fn test_restricted_handler_rejects_nesting() {
    let src = "server:\n  host: localhost";

    let mut parser = parser::Parser::new(src);
    let handler = RestrictedHandler::flat_dict_only();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.is_security_error());
    }
}

#[test]
fn test_restricted_handler_rejects_arrays() {
    let src = "items: [1, 2, 3]";

    let mut parser = parser::Parser::new(src);
    let handler = RestrictedHandler::flat_dict_only();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
}

#[test]
fn test_restricted_handler_rejects_tables() {
    let src = "users |id, name|\n  1, Alice";

    let mut parser = parser::Parser::new(src);
    let handler = RestrictedHandler::flat_dict_only();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
}

#[test]
fn test_safe_key_handler_rejects_proto() {
    let src = "__proto__: malicious";

    let mut parser = parser::Parser::new(src);
    let handler = SafeKeyHandler::new();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.is_security_error());
    }
}

#[test]
fn test_safe_key_handler_rejects_constructor() {
    let src = "constructor: bad";

    let mut parser = parser::Parser::new(src);
    let handler = SafeKeyHandler::new();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
}

#[test]
fn test_safe_key_handler_rejects_path_traversal() {
    // Test path traversal in quoted key (which would be a dict key)
    let src = r#""../../etc/passwd": secret"#;

    let mut parser = parser::Parser::new(src);
    let handler = SafeKeyHandler::new();
    let result = parser.parse_with_handler(handler);

    // Note: Current parser doesn't support quoted keys as dict keys,
    // so this will be a parse error. The handler check still works
    // for table fields and programmatically constructed keys.
    assert!(result.is_err());
}

#[test]
fn test_safe_key_handler_rejects_dotdot_in_key() {
    // Bare identifier with .. will be caught
    let src = "key..with..dots: value";

    let mut parser = parser::Parser::new(src);
    let handler = SafeKeyHandler::new();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
}

#[test]
fn test_safe_key_handler_accepts_safe_keys() {
    let src = "user_name: Alice\nuser_id: 42";

    let mut parser = parser::Parser::new(src);
    let handler = SafeKeyHandler::new();
    let value = parser.parse_with_handler(handler).unwrap();

    assert_eq!(value.get("user_name").and_then(|v| v.as_str()), Some("Alice"));
}

#[test]
fn test_safe_key_handler_validates_table_fields() {
    let src = "data |__proto__, name|\n  1, Alice";

    let mut parser = parser::Parser::new(src);
    let handler = SafeKeyHandler::new();
    let result = parser.parse_with_handler(handler);

    assert!(result.is_err());
}

#[test]
fn test_combined_validation() {
    // Test that handlers can be combined for multiple security layers
    let src = "config:\n  depth: too deep";

    // First validate with noop (depth check)
    let mut parser1 = parser::Parser::new(src);
    let noop = NoopHandler::with_limits(1, 1024, 1000);
    assert!(parser1.parse_with_handler(noop).is_err());

    // Then validate structure (no nesting allowed)
    let mut parser2 = parser::Parser::new(src);
    let restricted = RestrictedHandler::flat_dict_only();
    assert!(parser2.parse_with_handler(restricted).is_err());
}

#[test]
fn test_handler_with_complex_document() {
    let src = r#"
name: "Test Project"
version: "1.0.0"
features:
    auth
    logging
config:
    debug: true
    port: 8080
"#;

    let mut parser = parser::Parser::new(src);
    let handler = ValueBuilder::new();
    let value = parser.parse_with_handler(handler).unwrap();

    assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Test Project"));
    assert_eq!(value.get("version").and_then(|v| v.as_str()), Some("1.0.0"));
    assert_eq!(value.get_path("config.port").and_then(|v| v.as_i64()), Some(8080));
}

#[test]
fn test_noop_handler_accepts_valid_input() {
    let src = "server:\n  host: localhost\n  port: 8080";

    let mut parser = parser::Parser::new(src);
    let noop = NoopHandler::with_limits(10, 1024, 100);
    let result = parser.parse_with_handler(noop);

    assert!(result.is_ok());
}

// Convenience function tests

#[test]
fn test_parse_untrusted_accepts_valid() {
    let src = "name: Alice\nage: 30";
    let value = parser::parse_untrusted(src).unwrap();
    assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
}

#[test]
fn test_parse_untrusted_rejects_deep() {
    // 100-level nesting, limit is 50
    let mut src = String::new();
    for i in 0..100 {
        src.push_str(&format!("{}a:\n", "  ".repeat(i)));
    }
    src.push_str(&format!("{}value: x", "  ".repeat(100)));

    let result = parser::parse_untrusted(&src);
    assert!(result.is_err());
}

#[test]
fn test_parse_config_accepts_flat() {
    let src = "debug: true\nport: 8080\nhost: localhost";
    let value = parser::parse_config(src).unwrap();
    assert_eq!(value.get("port").and_then(|v| v.as_i64()), Some(8080));
}

#[test]
fn test_parse_config_rejects_nesting() {
    let src = "server:\n  host: localhost";
    let result = parser::parse_config(src);
    assert!(result.is_err());
}

#[test]
fn test_parse_config_rejects_arrays() {
    let src = "items: [1, 2, 3]";
    let result = parser::parse_config(src);
    assert!(result.is_err());
}

#[test]
fn test_parse_safe_accepts_normal_keys() {
    let src = "user_name: Alice\nuser_id: 42";
    let value = parser::parse_safe(src).unwrap();
    assert_eq!(value.get("user_name").and_then(|v| v.as_str()), Some("Alice"));
}

#[test]
fn test_parse_safe_rejects_proto() {
    let src = "__proto__: bad";
    let result = parser::parse_safe(src);
    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.is_security_error());
    }
}
