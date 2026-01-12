// SSpec docstring migration
// Converts print-based SSpec tests to intensive docstring format

use std::fs;
use std::path::Path;

/// Migrate a single file's SSpec print-based tests to docstring format
/// Returns Ok(true) if file was/would be modified, Ok(false) if no changes needed
pub fn migrate_file_sspec(path: &Path, dry_run: bool) -> Result<bool, String> {
    eprintln!("[MIGRATE_SSPEC] Processing file: {}", path.display());
    let content = fs::read_to_string(path).map_err(|e| format!("failed to read file: {}", e))?;

    let new_content = migrate_sspec_to_docstrings(&content);

    // Debug: Print comparison info
    #[cfg(debug_assertions)]
    {
        eprintln!("DEBUG: Original length: {}", content.len());
        eprintln!("DEBUG: New length: {}", new_content.len());
        if new_content != content {
            eprintln!("DEBUG: Content changed!");
        } else {
            eprintln!("DEBUG: Content unchanged");
        }
    }

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

/// Convert print-based SSpec patterns to intensive docstring format
fn migrate_sspec_to_docstrings(source: &str) -> String {
    let lines: Vec<&str> = source.lines().collect();
    eprintln!("DEBUG: Processing {} lines", lines.len());
    let mut result = Vec::new();
    let mut i = 0;
    let mut changes = 0;

    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim();

        // Check for print-based describe/context/it patterns
        // Use original line to preserve indentation for pattern matching
        if let Some(converted) = convert_print_line(line) {
            eprintln!("DEBUG: Converted line: {}", line);
            changes += 1;
            result.push(converted);
            i += 1;
            continue;
        }

        // Remove manual tracking lines
        if is_manual_tracking_line(trimmed) {
            i += 1;
            continue;
        }

        // Remove banner prints
        if is_banner_print(trimmed) {
            i += 1;
            continue;
        }

        // Keep other lines as-is
        result.push(line.to_string());
        i += 1;
    }

    eprintln!("DEBUG: Made {} changes", changes);
    result.join("\n")
}

/// Convert a single print line to SSpec syntax with docstring
fn convert_print_line(line: &str) -> Option<String> {
    // Pattern: print('describe...')
    if line.contains("print(") && line.contains("describe") {
        return extract_and_convert(line, "describe", 0);
    }

    // Pattern: print('  context...')
    if line.contains("print(") && line.contains("context") {
        return extract_and_convert(line, "context", 4);
    }

    // Pattern: print('    it...')
    if line.contains("print(") && line.contains("it ") {
        return extract_and_convert(line, "it", 8);
    }

    None
}

/// Extract text from print statement and convert to SSpec syntax
fn extract_and_convert(line: &str, keyword: &str, indent: usize) -> Option<String> {
    // Find the content between quotes
    let start = line.find(&['\'', '"'])?;
    let quote_char = line.chars().nth(start)?;
    let rest = &line[start + 1..];
    let end = rest.find(quote_char)?;
    let content = &rest[..end];

    // Remove leading spaces and keyword
    let mut text = content.trim_start();
    if text.starts_with(keyword) {
        text = &text[keyword.len()..].trim_start();
    }

    // Remove trailing colon if present
    text = text.trim_end_matches(':').trim();

    let indent_str = " ".repeat(indent);
    let docstring_indent = " ".repeat(indent + 4);

    Some(format!(
        "{}{} \"{}\":\n{}\"\"\"\n{}TODO: Add documentation here\n{}\"\"\"",
        indent_str, keyword, text, docstring_indent, docstring_indent, docstring_indent
    ))
}

/// Check if line is manual tracking (passed/failed variables)
fn is_manual_tracking_line(line: &str) -> bool {
    // Check for variable declarations/assignments
    if (line.contains("passed") || line.contains("failed")) {
        if line.contains("= 0") || line.contains("+ 1") {
            return true;
        }
    }

    // Check for [PASS]/[FAIL] print statements
    if line.contains("[PASS]") || line.contains("[FAIL]") {
        return true;
    }

    false
}

/// Check if line is a banner print statement
fn is_banner_print(line: &str) -> bool {
    if !line.contains("print(") {
        return false;
    }

    // Check for repeated separator characters
    line.contains("====")
        || line.contains("----")
        || line.contains("####")
        || line.contains("****")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_print_describe() {
        let input = "print('describe Docstring parsing:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"describe "Docstring parsing":"#));
        assert!(output.contains("\"\"\""));
    }

    #[test]
    fn test_convert_print_context() {
        let input = "print('  context extracts code blocks:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"context "extracts code blocks":"#));
        assert!(output.contains("\"\"\""));
    }

    #[test]
    fn test_convert_print_it() {
        let input = "print('    it finds code in docstrings:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"it "finds code in docstrings":"#));
        assert!(output.contains("\"\"\""));
    }

    #[test]
    fn test_is_manual_tracking_line() {
        assert!(is_manual_tracking_line("var passed = 0"));
        assert!(is_manual_tracking_line("passed = passed + 1"));
        assert!(is_manual_tracking_line("print('      [PASS] finds code blocks')"));
        assert!(!is_manual_tracking_line("val passed_test = true"));
    }

    #[test]
    fn test_is_banner_print() {
        assert!(is_banner_print("print('============================================================')"));
        assert!(is_banner_print("print('------------------------------------------------------------')"));
        assert!(!is_banner_print("print('regular message')"));
    }

    #[test]
    fn test_full_migration() {
        let input = r#"var passed = 0
var failed = 0

print('describe Docstring parsing:')
print('  context extracts code blocks:')
print('    it finds code in docstrings:')

if ex.code == "1 + 1":
    print('      [PASS] finds code blocks')
    passed = passed + 1"#;

        let output = migrate_sspec_to_docstrings(input);

        // Should have proper SSpec structure
        assert!(output.contains(r#"describe "Docstring parsing":"#));
        assert!(output.contains(r#"context "extracts code blocks":"#));
        assert!(output.contains(r#"it "finds code in docstrings":"#));

        // Should have docstrings
        assert!(output.contains("\"\"\""));

        // Should NOT have manual tracking
        assert!(!output.contains("var passed"));
        assert!(!output.contains("[PASS]"));
    }
}
