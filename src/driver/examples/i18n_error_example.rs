//! Example of using i18n diagnostics in the driver
//!
//! This example shows how to properly integrate i18n error reporting
//! in CLI commands.
//!
//! Run with: cargo run --example i18n_error_example

use simple_diagnostics::{Diagnostic, Severity, Span, i18n::ctx2};
use simple_diagnostics::formatters::TextFormatter;
use simple_parser::{Parser, ParseError};
use simple_driver::convert_parser_diagnostic;
use std::env;

fn main() {
    // Set language from command line or default to English
    let args: Vec<String> = env::args().collect();
    let lang = if let Some(lang_arg) = args.get(1) {
        lang_arg.as_str()
    } else {
        "en"
    };

    env::set_var("SIMPLE_LANG", lang);

    println!("=== Simple Compiler I18n Error Example ===");
    println!("Language: {}\n", lang);

    // Example 1: Parser error
    println!("Example 1: Parser Error (E0002 - Unexpected Token)");
    println!("---");

    let source1 = "fn main():\n    let x = [1, 2, 3  # Missing closing bracket";
    println!("Source:\n{}\n", source1);

    let mut parser = Parser::new(source1);
    match parser.parse() {
        Ok(_) => println!("Unexpected success!"),
        Err(parse_error) => {
            // Convert parser error to i18n diagnostic
            let i18n_diag = convert_parser_diagnostic(parse_error.to_diagnostic());

            // Format and display
            let formatter = TextFormatter::new();
            let output = formatter.format(&i18n_diag, source1);
            println!("{}\n", output);
        }
    }

    // Example 2: Compiler error (simulated)
    println!("\nExample 2: Compiler Error (E1001 - Undefined Variable)");
    println!("---");

    let source2 = "fn main():\n    let result = undefined_var + 42";
    println!("Source:\n{}\n", source2);

    let span = Span::new(30, 43, 2, 18);
    let ctx = ctx2("name", "undefined_var", "", "");
    let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx).with_span(span);

    let formatter = TextFormatter::new();
    let output = formatter.format(&diag, source2);
    println!("{}\n", output);

    // Example 3: Type mismatch error
    println!("\nExample 3: Type Mismatch (E1003)");
    println!("---");

    let source3 = "fn add(x: i64, y: i64) -> i64:\n    return x + y\n\nadd(\"hello\", 42)";
    println!("Source:\n{}\n", source3);

    let span = Span::new(52, 59, 4, 5);
    let ctx = ctx2("expected", "i64", "found", "String");
    let diag = Diagnostic::error_i18n("compiler", "E1003", &ctx)
        .with_span(span)
        .with_note("String cannot be converted to i64 in this context");

    let formatter = TextFormatter::new();
    let output = formatter.format(&diag, source3);
    println!("{}\n", output);

    // Example 4: Multiple errors
    println!("\nExample 4: Multiple Errors");
    println!("---");

    let source4 = "fn test():\n    x + y  # Both undefined";
    println!("Source:\n{}\n", source4);

    let diagnostics = vec![
        {
            let ctx = ctx2("name", "x", "", "");
            Diagnostic::error_i18n("compiler", "E1001", &ctx).with_span(Span::new(15, 16, 2, 5))
        },
        {
            let ctx = ctx2("name", "y", "", "");
            Diagnostic::error_i18n("compiler", "E1001", &ctx).with_span(Span::new(19, 20, 2, 9))
        },
    ];

    let formatter = TextFormatter::new();
    for diag in &diagnostics {
        let output = formatter.format(diag, source4);
        println!("{}", output);
    }

    println!("\n=== Integration Guide ===");
    println!("To integrate i18n errors in CLI commands:");
    println!("1. Use convert_parser_diagnostic() for parser errors");
    println!("2. Use Diagnostic::error_i18n() for compiler errors");
    println!("3. Use TextFormatter to display errors");
    println!("4. Set SIMPLE_LANG environment variable for locale");
}
