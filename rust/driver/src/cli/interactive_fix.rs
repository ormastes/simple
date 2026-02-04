//! Interactive fix prompt for --fix-interactive mode.
//!
//! Presents each fix to the user and asks whether to apply it.

use simple_common::diagnostic::EasyFix;
use std::io::{self, BufRead, Write};

/// Prompt the user for each fix. Returns the fixes they accepted.
pub fn prompt_fixes<'a>(fixes: &[&'a EasyFix]) -> Vec<&'a EasyFix> {
    let mut accepted = Vec::new();
    let stdin = io::stdin();
    let mut reader = stdin.lock();

    for (i, fix) in fixes.iter().enumerate() {
        println!();
        println!(
            "Fix {}/{}: [{}] (confidence: {:?})",
            i + 1,
            fixes.len(),
            fix.id,
            fix.confidence,
        );
        println!("  {}", fix.description);
        for rep in &fix.replacements {
            println!(
                "  {} [{}:{}] -> \"{}\"",
                rep.file, rep.span.line, rep.span.column, rep.new_text
            );
        }
        print!("  [y]es / [n]o / [a]ll / [q]uit > ");
        io::stdout().flush().ok();

        let mut input = String::new();
        if reader.read_line(&mut input).is_err() {
            break;
        }

        match input.trim().to_lowercase().as_str() {
            "y" | "yes" => {
                accepted.push(*fix);
            }
            "a" | "all" => {
                accepted.push(*fix);
                // Accept all remaining
                for remaining in &fixes[i + 1..] {
                    accepted.push(*remaining);
                }
                break;
            }
            "q" | "quit" => {
                break;
            }
            _ => {
                // Skip (n or anything else)
            }
        }
    }

    accepted
}
