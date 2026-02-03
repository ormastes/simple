//! Print syntax migration
//!
//! Migrates old print/println syntax to new semantics:
//! - println() → print() (with newline)
//! - print() → print_raw() (no newline)
//! - eprintln() → eprint() (with newline)
//! - eprint() → eprint_raw() (no newline)

use std::fs;
use std::path::Path;

use super::file_walker;

/// Migrate print/println syntax
pub fn migrate_print_syntax(path: &Path, dry_run: bool) -> i32 {
    if !path.exists() {
        eprintln!("error: path does not exist: {}", path.display());
        return 1;
    }

    let files = file_walker::collect_spl_files(path);

    if files.is_empty() {
        println!("No .spl files found in {}", path.display());
        return 0;
    }

    if dry_run {
        println!("DRY RUN: Previewing changes to {} file(s)...", files.len());
    } else {
        println!("Migrating {} file(s)...", files.len());
    }

    let mut modified_count = 0;
    let mut error_count = 0;

    for file in &files {
        match migrate_file_print(file, dry_run) {
            Ok(true) => {
                modified_count += 1;
                if dry_run {
                    println!("  ⚠ {} (would be modified)", file.display());
                } else {
                    println!("  ✓ {}", file.display());
                }
            }
            Ok(false) => {
                // No changes needed
            }
            Err(e) => {
                error_count += 1;
                eprintln!("  ✗ {}: {}", file.display(), e);
            }
        }
    }

    if dry_run {
        file_walker::print_dry_run_summary(modified_count, files.len(), error_count);
    } else {
        file_walker::print_migration_summary(modified_count, files.len(), error_count);
    }

    if error_count > 0 {
        1
    } else {
        0
    }
}

/// Migrate a single file's print syntax
/// Returns Ok(true) if file was/would be modified, Ok(false) if no changes needed
fn migrate_file_print(path: &Path, dry_run: bool) -> Result<bool, String> {
    let content = fs::read_to_string(path).map_err(|e| format!("failed to read file: {}", e))?;

    let new_content = migrate_print_calls(&content);

    if new_content == content {
        // No changes needed
        return Ok(false);
    }

    // Write back only if not in dry-run mode
    if !dry_run {
        fs::write(path, new_content).map_err(|e| format!("failed to write file: {}", e))?;
    }

    Ok(true)
}

/// Migrate print/println syntax
/// Old: print (no newline), println (with newline)
/// New: print (with newline), print_raw (no newline)
fn migrate_print_calls(source: &str) -> String {
    let chars: Vec<char> = source.chars().collect();
    let mut result = String::with_capacity(source.len() + 100);
    let mut i = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let mut escape_next = false;

    while i < chars.len() {
        let ch = chars[i];

        if escape_next {
            escape_next = false;
            result.push(ch);
            i += 1;
            continue;
        }

        match ch {
            '\\' if in_string => {
                escape_next = true;
                result.push(ch);
                i += 1;
                continue;
            }
            '"' if !in_comment => {
                in_string = !in_string;
                result.push(ch);
                i += 1;
                continue;
            }
            '#' if !in_string => {
                in_comment = true;
                result.push(ch);
                i += 1;
                continue;
            }
            '\n' => {
                in_comment = false;
                result.push(ch);
                i += 1;
                continue;
            }
            _ => {}
        }

        if in_string || in_comment {
            result.push(ch);
            i += 1;
            continue;
        }

        // Check for function calls: println, print, eprintln, eprint
        if ch == 'p' || ch == 'e' {
            if let Some(replacement) = try_replace_print_call(&chars, i) {
                result.push_str(&replacement.new_text);
                i += replacement.consumed_len;
            } else {
                result.push(ch);
                i += 1;
            }
        } else {
            result.push(ch);
            i += 1;
        }
    }

    result
}

struct Replacement {
    new_text: String,
    consumed_len: usize,
}

/// Try to replace print call at position
fn try_replace_print_call(chars: &[char], pos: usize) -> Option<Replacement> {
    let remaining: String = chars[pos..].iter().take(20).collect();

    // Match patterns and their replacements
    // Priority order matters: check longer patterns first
    if remaining.starts_with("println(") {
        Some(Replacement {
            new_text: "print(".to_string(),
            consumed_len: "println(".len(),
        })
    } else if remaining.starts_with("eprintln(") {
        Some(Replacement {
            new_text: "eprint(".to_string(),
            consumed_len: "eprintln(".len(),
        })
    } else if remaining.starts_with("print(") {
        Some(Replacement {
            new_text: "print_raw(".to_string(),
            consumed_len: "print(".len(),
        })
    } else if remaining.starts_with("eprint(") {
        Some(Replacement {
            new_text: "eprint_raw(".to_string(),
            consumed_len: "eprint(".len(),
        })
    } else {
        None
    }
}
