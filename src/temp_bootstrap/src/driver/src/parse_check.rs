// Quick parse checker binary
// Usage: find src/ test/ -name '*.spl' | parse_check
// Token dump: parse_check --tokens < file_list

use std::env;
use std::fs;
use std::io::{self, BufRead};

fn main() {
    let args: Vec<String> = env::args().collect();
    let dump_tokens = args.iter().any(|a| a == "--tokens");

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

        if dump_tokens {
            println!("=== Tokens for {} ===", path);
            let mut lexer = simple_parser::lexer::Lexer::new(&source);
            loop {
                let tok = lexer.next_token();
                println!("  {:?} @ {}:{}", tok.kind, tok.span.line, tok.span.column);
                if tok.kind == simple_parser::token::TokenKind::Eof {
                    break;
                }
            }
            continue;
        }

        let mut parser = simple_parser::parser::Parser::new(&source);
        match parser.parse() {
            Ok(_) => {},
            Err(e) => {
                errors += 1;
                let line_info = if let Some(span) = e.span() {
                    format!(" [line {}:{}]", span.line, span.column)
                } else {
                    String::new()
                };
                let msg = format!("{}{}", e, line_info);
                error_msgs.push((path, msg));
            }
        }
    }

    if dump_tokens { return; }

    // Print errors
    for (path, msg) in &error_msgs {
        println!("Parse error in {}: {}", path, msg);
    }

    println!("\n=== Summary ===");
    println!("Total files: {}", total);
    println!("Parsed OK: {}", total - errors);
    println!("Parse errors: {}", errors);
    if total > 0 {
        println!("Parse rate: {:.1}%", (total - errors) as f64 / total as f64 * 100.0);
    }
}
