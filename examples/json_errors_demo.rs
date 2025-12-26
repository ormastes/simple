// Demo: JSON Error Format for LLM Tools
// This example shows how to use the new JSON serialization feature

use simple_common::diagnostic::{Diagnostic, Diagnostics, Severity, Span};

fn main() {
    println!("=== JSON Error Format Demo (#888) ===\n");

    // Create a collection of diagnostics
    let mut diags = Diagnostics::new();

    // Add an error
    diags.push(
        Diagnostic::error("type mismatch")
            .with_code("E0308")
            .with_file("example.spl")
            .with_label(
                Span::new(45, 50, 3, 12),
                "expected i64, found str"
            )
            .with_help("try converting the string to an integer")
            .with_note("types must match exactly in assignments")
    );

    // Add a warning
    diags.push(
        Diagnostic::warning("unused variable")
            .with_code("W0001")
            .with_file("example.spl")
            .with_label(
                Span::new(20, 25, 2, 9),
                "variable `count` is never used"
            )
            .with_help("prefix with `_` to silence this warning")
    );

    // Output as pretty JSON
    println!("Pretty JSON Output:");
    println!("{}\n", diags.to_json().unwrap());

    // Output as compact JSON
    println!("Compact JSON Output (for piping):");
    println!("{}\n", diags.to_json_compact().unwrap());

    // Show statistics
    println!("Statistics:");
    println!("  Errors:   {}", diags.error_count());
    println!("  Warnings: {}", diags.warning_count());
    println!("  Total:    {}", diags.len());
}
