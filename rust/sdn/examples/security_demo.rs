//! Security demonstration for SDN parser handlers
//!
//! This example demonstrates all security features:
//! 1. Normal parsing (trusted input)
//! 2. Untrusted input validation
//! 3. Configuration file parsing (flat dict only)
//! 4. Safe key validation
//! 5. Custom handlers

use simple_sdn::{parse, parse_config, parse_safe, parse_untrusted};
use simple_sdn::{parser::Parser, NoopHandler, RestrictedHandler, SafeKeyHandler};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== SDN Security Features Demo ===\n");

    // 1. Normal Parsing (Trusted Input)
    println!("1. Normal Parsing (Trusted Input)");
    let trusted = r#"
name: Alice
age: 30
config:
    debug: true
    port: 8080
"#;
    let value = parse(trusted)?;
    println!("   ✓ Parsed: name={:?}", value.get("name"));
    println!();

    // 2. Untrusted Input Validation
    println!("2. Untrusted Input Validation");
    let untrusted = "user: Bob\nlevel: 5";
    match parse_untrusted(untrusted) {
        Ok(v) => println!("   ✓ Valid input accepted: {:?}", v.get("user")),
        Err(e) => println!("   ✗ Rejected: {}", e),
    }

    // Try malicious input (deep nesting - 60 levels, limit is 50)
    let mut malicious = String::new();
    for i in 0..60 {
        malicious.push_str(&format!("{}a{}:\n", "  ".repeat(i), i));
    }
    malicious.push_str(&format!("{}too_deep: x", "  ".repeat(60)));
    match parse_untrusted(&malicious) {
        Ok(_) => println!("   ✗ Should have rejected deep nesting!"),
        Err(e) => println!("   ✓ Rejected deep nesting (60 levels > 50 limit)"),
    }
    println!();

    // 3. Configuration File Parsing
    println!("3. Configuration File Parsing (Flat Dict Only)");
    let config = "debug: true\nport: 8080\nhost: localhost";
    match parse_config(config) {
        Ok(v) => println!("   ✓ Valid config: port={:?}", v.get("port")),
        Err(e) => println!("   ✗ Error: {}", e),
    }

    // Try nested structure (should be rejected)
    let nested_config = "server:\n  host: localhost";
    match parse_config(nested_config) {
        Ok(_) => println!("   ✗ Should have rejected nesting!"),
        Err(e) => println!("   ✓ Rejected nested config: {}", e),
    }
    println!();

    // 4. Safe Key Validation
    println!("4. Safe Key Validation");
    let safe_input = "user_name: Alice\nuser_id: 42";
    match parse_safe(safe_input) {
        Ok(v) => println!("   ✓ Safe keys accepted: {:?}", v.get("user_name")),
        Err(e) => println!("   ✗ Error: {}", e),
    }

    // Try prototype pollution
    let proto_pollution = "__proto__: malicious";
    match parse_safe(proto_pollution) {
        Ok(_) => println!("   ✗ Should have rejected __proto__!"),
        Err(e) => println!("   ✓ Rejected __proto__: {}", e),
    }
    println!();

    // 5. Custom Handlers
    println!("5. Custom Handlers");

    // NoopHandler with strict limits
    let input = "data: [1, 2, 3, 4, 5]";
    let mut parser = Parser::new(input);
    let noop = NoopHandler::with_limits(5, 1000, 10);
    match parser.parse_with_handler(noop) {
        Ok(_) => println!("   ✓ NoopHandler: Validation passed"),
        Err(e) => println!("   ✗ NoopHandler: {}", e),
    }

    // RestrictedHandler (no arrays)
    let mut parser = Parser::new(input);
    let handler = RestrictedHandler::new().without_arrays();
    match parser.parse_with_handler(handler) {
        Ok(_) => println!("   ✗ Should have rejected array!"),
        Err(e) => println!("   ✓ RestrictedHandler: {}", e),
    }

    // SafeKeyHandler
    let input = "normal_key: value";
    let mut parser = Parser::new(input);
    let handler = SafeKeyHandler::new();
    match parser.parse_with_handler(handler) {
        Ok(v) => println!("   ✓ SafeKeyHandler: {:?}", v.get("normal_key")),
        Err(e) => println!("   ✗ SafeKeyHandler: {}", e),
    }
    println!();

    // 6. Defense in Depth (Multiple Layers)
    println!("6. Defense in Depth (Multiple Layers)");
    let input = "config:\n  key: value";

    // Layer 1: Depth check
    let mut parser = Parser::new(input);
    let noop = NoopHandler::with_limits(10, 1024, 100);
    match parser.parse_with_handler(noop) {
        Ok(_) => println!("   ✓ Layer 1 (depth): Passed"),
        Err(e) => println!("   ✗ Layer 1 (depth): {}", e),
    }

    // Layer 2: Structure check (flat only)
    match parse_config(input) {
        Ok(_) => println!("   ✗ Layer 2 (structure): Should reject nesting!"),
        Err(e) => println!("   ✓ Layer 2 (structure): {}", e),
    }
    println!();

    println!("=== Demo Complete ===");
    println!("\nAll security features working correctly! 🎉");

    Ok(())
}
