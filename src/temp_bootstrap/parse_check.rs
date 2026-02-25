// Quick parse checker - compile with:
// rustc --edition 2021 -L target/debug/deps --extern simple_parser=target/debug/libsimple_parser-*.rlib parse_check.rs -o parse_check

use std::env;
use std::fs;
use std::io::{self, BufRead};

fn main() {
    // Read file paths from stdin
    let stdin = io::stdin();
    let mut total = 0;
    let mut errors = 0;
    let mut error_msgs: Vec<(String, String)> = Vec::new();

    for line in stdin.lock().lines() {
        let path = match line {
            Ok(p) => p.trim().to_string(),
            Err(_) => continue,
        };
        if path.is_empty() { continue; }

        total += 1;
        let source = match fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Cannot read {}: {}", path, e);
                continue;
            }
        };

        let mut parser = simple_parser::parser::Parser::new(&source);
        match parser.parse() {
            Ok(_) => {},
            Err(e) => {
                errors += 1;
                let msg = format!("{}", e);
                error_msgs.push((path, msg));
            }
        }
    }

    // Print errors
    for (path, msg) in &error_msgs {
        println!("Parse error in {}: {}", path, msg);
    }

    println!("\n=== Summary ===");
    println!("Total files: {}", total);
    println!("Parsed OK: {}", total - errors);
    println!("Parse errors: {}", errors);
    println!("Parse rate: {:.1}%", (total - errors) as f64 / total as f64 * 100.0);
}
