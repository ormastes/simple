//! Code migration commands for Simple language.
//!
//! Provides automated migration tools for syntax changes and deprecations.

use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use super::migrate_sspec;

/// Run migration command
pub fn run_migrate(args: &[String]) -> i32 {
    // args[0] is "migrate", args[1] is the subcommand
    if args.len() < 2 || args.iter().any(|a| a == "--help" || a == "-h") {
        print_migrate_help();
        return 0;
    }

    let subcommand = &args[1];
    match subcommand.as_str() {
        "--fix-generics" => {
            // Check for --dry-run flag
            let dry_run = args.iter().any(|a| a == "--dry-run" || a == "-n");

            // Find path argument (skip --dry-run flags)
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("."));

            migrate_generics(&path, dry_run)
        }
        "--fix-print" => {
            // Check for --dry-run flag
            let dry_run = args.iter().any(|a| a == "--dry-run" || a == "-n");

            // Find path argument (skip --dry-run flags)
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("."));

            migrate_print_syntax(&path, dry_run)
        }
        "--fix-sspec-docstrings" => {
            // Check for --dry-run flag
            let dry_run = args.iter().any(|a| a == "--dry-run" || a == "-n");

            // Find path argument (skip --dry-run flags)
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("."));

            migrate_sspec_docstrings(&path, dry_run)
        }
        _ => {
            eprintln!("error: unknown migration subcommand: {}", subcommand);
            eprintln!("Run 'simple migrate --help' for usage");
            1
        }
    }
}

fn print_migrate_help() {
    println!("Migration tools for Simple language syntax changes");
    println!();
    println!("Usage:");
    println!("  simple migrate --fix-generics [OPTIONS] [path]");
    println!("  simple migrate --fix-print [OPTIONS] [path]");
    println!("  simple migrate --fix-sspec-docstrings [OPTIONS] [path]");
    println!();
    println!("Migrations:");
    println!("  --fix-generics <path>    Convert [] generic syntax to <>");
    println!("                           Example: List[T] → List<T>");
    println!("                           Processes all .spl files in path");
    println!();
    println!("  --fix-print <path>       Migrate print/println syntax");
    println!("                           println() → print()");
    println!("                           print() → print_raw()");
    println!("                           eprintln() → eprint()");
    println!("                           eprint() → eprint_raw()");
    println!("                           Processes all .spl files in path");
    println!();
    println!("  --fix-sspec-docstrings   Convert print-based SSpec tests to docstrings");
    println!("           <path>          Converts: print('describe...')");
    println!("                           To: describe \"...\":");
    println!("                                   \"\"\"Documentation\"\"\"");
    println!("                           Processes *_spec.spl files only");
    println!();
    println!("Options:");
    println!("  -n, --dry-run           Preview changes without modifying files");
    println!("  -h, --help              Show this help message");
    println!();
    println!("Examples:");
    println!("  simple migrate --fix-generics src/");
    println!("  simple migrate --fix-generics my_file.spl");
    println!("  simple migrate --fix-generics --dry-run src/");
    println!("  simple migrate --fix-print simple/std_lib/");
    println!("  simple migrate --fix-print --dry-run .");
    println!("  simple migrate --fix-sspec-docstrings simple/std_lib/test/features/");
    println!("  simple migrate --fix-sspec-docstrings --dry-run tests/");
}

/// Migrate generic syntax from [] to <>
fn migrate_generics(path: &Path, dry_run: bool) -> i32 {
    if !path.exists() {
        eprintln!("error: path does not exist: {}", path.display());
        return 1;
    }

    let files = if path.is_file() {
        vec![path.to_path_buf()]
    } else {
        // Walk directory and find all .spl files
        WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
            .map(|e| e.path().to_path_buf())
            .collect::<Vec<_>>()
    };

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
        match migrate_file_generics(file, dry_run) {
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

    println!();
    if dry_run {
        println!("DRY RUN complete!");
        println!("  Would modify: {}", modified_count);
        println!(
            "  Unchanged: {}",
            files.len() - modified_count - error_count
        );
        println!("  Errors: {}", error_count);
        if modified_count > 0 {
            println!();
            println!("Run without --dry-run to apply these changes");
        }
    } else {
        println!("Migration complete!");
        println!("  Modified: {}", modified_count);
        println!(
            "  Unchanged: {}",
            files.len() - modified_count - error_count
        );
        println!("  Errors: {}", error_count);
    }

    if error_count > 0 {
        1
    } else {
        0
    }
}

/// Migrate a single file's generic syntax
/// Returns Ok(true) if file was/would be modified, Ok(false) if no changes needed
fn migrate_file_generics(path: &Path, dry_run: bool) -> Result<bool, String> {
    let content = fs::read_to_string(path).map_err(|e| format!("failed to read file: {}", e))?;

    let new_content = migrate_generic_syntax(&content);

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

/// Migrate generic syntax from [] to <>
/// This is a two-pass implementation that properly tracks bracket conversions
fn migrate_generic_syntax(source: &str) -> String {
    // First pass: identify which brackets should be converted
    let chars: Vec<char> = source.chars().collect();
    let mut bracket_conversions = vec![false; chars.len()]; // Track which '[' positions to convert
    let mut bracket_stack: Vec<usize> = Vec::new(); // Stack of '[' positions
    let mut in_string = false;
    let mut in_comment = false;
    let mut escape_next = false;

    // Pass 1: Mark brackets for conversion
    for i in 0..chars.len() {
        let ch = chars[i];

        if escape_next {
            escape_next = false;
            continue;
        }

        match ch {
            '\\' if in_string => {
                escape_next = true;
                continue;
            }
            '"' if !in_comment => {
                in_string = !in_string;
                continue;
            }
            '#' if !in_string => {
                in_comment = true;
                continue;
            }
            '\n' => {
                in_comment = false;
                continue;
            }
            _ => {}
        }

        if in_string || in_comment {
            continue;
        }

        if ch == '[' {
            // Check if this should be a generic bracket
            if is_generic_bracket_at_pos(&chars, i) {
                bracket_conversions[i] = true;
                bracket_stack.push(i);
            } else {
                bracket_stack.push(i);
            }
        } else if ch == ']' {
            // Match with opening bracket
            if let Some(open_pos) = bracket_stack.pop() {
                // Only convert if the opening bracket was converted
                if bracket_conversions[open_pos] {
                    bracket_conversions[i] = true;
                }
            }
        }
    }

    // Pass 2: Build result with conversions
    let mut result = String::with_capacity(source.len());
    for (i, &ch) in chars.iter().enumerate() {
        if bracket_conversions[i] {
            if ch == '[' {
                result.push('<');
            } else if ch == ']' {
                result.push('>');
            } else {
                result.push(ch);
            }
        } else {
            result.push(ch);
        }
    }

    result
}

/// Check if the '[' at position i should be converted to '<'
fn is_generic_bracket_at_pos(chars: &[char], pos: usize) -> bool {
    // Look backward to find context
    let before: String = chars[..pos].iter().collect();
    let after: String = if pos + 1 < chars.len() {
        chars[pos + 1..].iter().take(20).collect()
    } else {
        String::new()
    };

    let trimmed_before = before.trim_end();

    // Rule 1: After '=' is array literal, not generic
    if trimmed_before.ends_with('=') {
        return false;
    }

    // Rule 2: Check if preceded by an identifier
    if let Some(last_char) = trimmed_before.chars().last() {
        if last_char.is_alphanumeric() || last_char == '_' || last_char == '>' {
            // Extract the identifier before [
            let mut ident = String::new();
            for ch in trimmed_before.chars().rev() {
                if ch.is_alphanumeric() || ch == '_' {
                    ident.insert(0, ch);
                } else {
                    break;
                }
            }

            // Check for capitalized type names (List, Option, Result, etc.)
            if !ident.is_empty() {
                let first_char = ident.chars().next().unwrap();
                if first_char.is_uppercase() {
                    // But check if this is array type syntax like [i32]
                    // by checking if after[ we have lowercase primitive followed by ]
                    let after_trimmed = after.trim_start();
                    if is_array_type_syntax(after_trimmed) {
                        return false;
                    }
                    return true;
                }
            }

            // Check context: after keywords
            let keywords = ["fn", "struct", "class", "enum", "impl", "trait", "type"];
            for kw in &keywords {
                if trimmed_before.ends_with(kw) {
                    return true;
                }
            }

            // Check if after ':' (type annotation) - but not array type
            let before_ident = trimmed_before
                .trim_end_matches(|c: char| c.is_alphanumeric() || c == '_')
                .trim_end();
            if before_ident.ends_with(':') {
                // Check if this looks like array type [i32] or generic Option[T]
                if !ident.is_empty() {
                    let first_char = ident.chars().next().unwrap();
                    // Lowercase after : might be array type marker
                    if first_char.is_lowercase() {
                        return false;
                    }
                } else {
                    // No identifier before [, might be array type like : [i32]
                    return false;
                }
                return true;
            }
        }
    }

    // Rule 3: Check what's inside the brackets
    let after_trimmed = after.trim_start();

    // IMPORTANT: Check for array type syntax FIRST, before uppercase check
    // This catches [T; N] and [i32; 10] before we mistakenly think T is a type param
    if is_array_type_syntax(after_trimmed) {
        return false;
    }

    if let Some(first) = after_trimmed.chars().next() {
        // Check for array literal patterns like [1, 2, 3]
        if first.is_numeric() {
            return false;
        }
        // Type parameter like T, U, V or type name (uppercase)
        if first.is_uppercase() {
            return true;
        }
        // Keyword 'const' for const generics
        if after_trimmed.starts_with("const") {
            return true;
        }
    }

    false
}

/// Check if the content looks like array type syntax
/// Examples: "i32]", "i32; 10]", "T; N]"
fn is_array_type_syntax(content: &str) -> bool {
    // Check for patterns: primitive_type] or type; size]
    if content.contains(';') {
        return true; // Fixed-size array like [T; 10]
    }

    // Check if it's a primitive type followed by ]
    let primitives = [
        "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "f32", "f64", "bool",
        "char",
    ];

    for prim in &primitives {
        if content.starts_with(prim) {
            let rest = &content[prim.len()..].trim_start();
            if rest.starts_with(']') {
                return true;
            }
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_migrate_simple_generic() {
        let input = "fn test[T](x: T) -> T:";
        let expected = "fn test<T>(x: T) -> T:";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_migrate_type_annotation() {
        let input = "val x: Option[Int]";
        let expected = "val x: Option<Int>";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_migrate_nested() {
        let input = "val x: List[Option[String]]";
        let expected = "val x: List<Option<String>>";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_preserve_array_literal() {
        let input = "val arr = [1, 2, 3]";
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_preserve_array_type() {
        let input = "val arr: [i32]";
        // Array type should stay as [i32]
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_preserve_indexing() {
        let input = "val x = arr[0]";
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_ignore_in_string() {
        let input = r#"val s = "List[T]""#;
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_ignore_in_comment() {
        let input = "# List[T] example";
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_comprehensive_mixed() {
        let input = r#"fn test[T](x: T) -> T:
    x

val my_list: List[Int] = []
val opt: Option[String] = None
val arr: [i32] = [1, 2, 3]
val nested: List[Option[Result[T, E]]] = []"#;
        let expected = r#"fn test<T>(x: T) -> T:
    x

val my_list: List<Int> = []
val opt: Option<String> = None
val arr: [i32] = [1, 2, 3]
val nested: List<Option<Result<T, E>>> = []"#;
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_struct_generic() {
        let input = "struct Container[T]:\n    value: T";
        let expected = "struct Container<T>:\n    value: T";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_impl_generic() {
        let input = "impl[T] Container[T]:\n    fn new(val: T) -> Container[T]:\n        pass";
        let expected = "impl<T> Container<T>:\n    fn new(val: T) -> Container<T>:\n        pass";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_fixed_array_type() {
        let input = "val arr: [i32; 10] = []";
        // Array type should stay as [i32; 10]
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_array_indexing() {
        let input = "val elem = arr[0]\nval cell = matrix[i][j]";
        assert_eq!(migrate_generic_syntax(input), input);
    }

    #[test]
    fn test_multiple_generics_on_line() {
        let input = "fn map[T, U](x: List[T], f: fn(T) -> U) -> List[U]:";
        let expected = "fn map<T, U>(x: List<T>, f: fn(T) -> U) -> List<U>:";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_enum_generic() {
        let input = "enum Result[T, E]:\n    Ok(T)\n    Err(E)";
        let expected = "enum Result<T, E>:\n    Ok(T)\n    Err(E)";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_trait_generic() {
        let input = "trait Iterator[T]:\n    fn next() -> Option[T]";
        let expected = "trait Iterator<T>:\n    fn next() -> Option<T>";
        assert_eq!(migrate_generic_syntax(input), expected);
    }

    #[test]
    fn test_const_generic() {
        let input = "struct Array[T, const N: usize]:\n    data: [T; N]";
        let expected = "struct Array<T, const N: usize>:\n    data: [T; N]";
        assert_eq!(migrate_generic_syntax(input), expected);
    }
}

/// Migrate print/println syntax
fn migrate_print_syntax(path: &Path, dry_run: bool) -> i32 {
    if !path.exists() {
        eprintln!("error: path does not exist: {}", path.display());
        return 1;
    }

    let files = if path.is_file() {
        vec![path.to_path_buf()]
    } else {
        // Walk directory and find all .spl files
        WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
            .map(|e| e.path().to_path_buf())
            .collect::<Vec<_>>()
    };

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
        match migrate_file_print(&file, dry_run) {
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

    println!();
    if dry_run {
        println!("DRY RUN complete!");
        println!("  Would modify: {}", modified_count);
        println!(
            "  Unchanged: {}",
            files.len() - modified_count - error_count
        );
        println!("  Errors: {}", error_count);
        if modified_count > 0 {
            println!();
            println!("Run without --dry-run to apply these changes");
        }
    } else {
        println!("Migration complete!");
        println!("  Modified: {}", modified_count);
        println!(
            "  Unchanged: {}",
            files.len() - modified_count - error_count
        );
        println!("  Errors: {}", error_count);
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

/// Migrate print-based SSpec tests to intensive docstring format
fn migrate_sspec_docstrings(path: &Path, dry_run: bool) -> i32 {
    if !path.exists() {
        eprintln!("error: path does not exist: {}", path.display());
        return 1;
    }

    let files = if path.is_file() {
        vec![path.to_path_buf()]
    } else {
        // Walk directory and find all *_spec.spl files
        WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .file_name()
                    .and_then(|n| n.to_str())
                    .map(|n| n.ends_with("_spec.spl"))
                    .unwrap_or(false)
            })
            .map(|e| e.path().to_path_buf())
            .collect::<Vec<_>>()
    };

    if files.is_empty() {
        println!("No *_spec.spl files found in {}", path.display());
        return 0;
    }

    if dry_run {
        println!("DRY RUN: Previewing SSpec docstring migration for {} file(s)...", files.len());
    } else {
        println!("Migrating {} SSpec test file(s) to intensive docstring format...", files.len());
    }

    let mut modified_count = 0;
    let mut error_count = 0;
    let mut skipped_count = 0;

    for file in &files {
        match migrate_sspec::migrate_file_sspec(file, dry_run) {
            Ok(true) => {
                modified_count += 1;
                if dry_run {
                    println!("  ⚠  {} (would be modified)", file.display());
                } else {
                    println!("  ✓  {}", file.display());
                }
            }
            Ok(false) => {
                skipped_count += 1;
                // No changes needed - likely already in docstring format
            }
            Err(e) => {
                error_count += 1;
                eprintln!("  ✗  {}: {}", file.display(), e);
            }
        }
    }

    println!();
    if dry_run {
        println!("DRY RUN complete!");
        println!("  Would modify: {}", modified_count);
        println!("  Already correct: {}", skipped_count);
        println!("  Errors: {}", error_count);
        if modified_count > 0 {
            println!();
            println!("Run without --dry-run to apply these changes");
            println!("IMPORTANT: Review changes carefully before committing!");
            println!("See doc/examples/sspec_conversion_example.md for migration guide");
        }
    } else {
        println!("Migration complete!");
        println!("  Modified: {}", modified_count);
        println!("  Already correct: {}", skipped_count);
        println!("  Errors: {}", error_count);
        if modified_count > 0 {
            println!();
            println!("⚠  IMPORTANT: Review all changes before committing!");
            println!("   - Check that test logic is preserved");
            println!("   - Add comprehensive docstring documentation");
            println!("   - Run tests to verify functionality");
            println!();
            println!("See doc/examples/sspec_conversion_example.md for best practices");
        }
    }

    if error_count > 0 {
        1
    } else {
        0
    }
}
