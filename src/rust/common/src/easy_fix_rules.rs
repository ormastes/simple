//! EasyFix Rules — thin bridge to Simple implementation
//!
//! Instead of duplicating rule logic in Rust, this module provides:
//! 1. A bridge to call the Simple rules (`src/app/fix/rules.spl`) via the interpreter FFI
//! 2. Conversion from interpreter `Value` → Rust `EasyFix` structs
//! 3. Helper functions for rules that need compiler integration (typo, type coercion)
//!
//! Design rationale: "Impl in Simple unless it has big performance differences" (CLAUDE.md)
//! Text-scanning lint rules don't need Rust-level performance.

use crate::diagnostic::{EasyFix, FixConfidence, Replacement, Span};

// ============================================================================
// Levenshtein distance (needed for typo suggestions in name resolution)
// This one stays in Rust because it's called from the compiler's name resolver.
// ============================================================================

/// Compute Levenshtein edit distance between two strings.
pub fn levenshtein(a: &str, b: &str) -> usize {
    let m = a.len();
    let n = b.len();
    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    let a_bytes = a.as_bytes();
    let b_bytes = b.as_bytes();

    let mut prev: Vec<usize> = (0..=n).collect();
    let mut curr = vec![0; n + 1];

    for i in 1..=m {
        curr[0] = i;
        for j in 1..=n {
            let cost = if a_bytes[i - 1] == b_bytes[j - 1] { 0 } else { 1 };
            curr[j] = (prev[j] + 1)
                .min(curr[j - 1] + 1)
                .min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[n]
}

/// Suggest a typo fix for a misspelled identifier.
///
/// Returns an EasyFix if a known name is within edit distance 2.
pub fn suggest_typo_fix(
    file: &str,
    line: usize,
    column: usize,
    byte_start: usize,
    byte_end: usize,
    misspelled: &str,
    known_names: &[&str],
) -> Option<EasyFix> {
    let mut best_name = "";
    let mut best_dist = 3usize; // max threshold

    for &name in known_names {
        let dist = levenshtein(misspelled, name);
        if dist > 0 && dist < best_dist {
            best_dist = dist;
            best_name = name;
        }
    }

    if !best_name.is_empty() {
        Some(EasyFix {
            id: format!("E:typo_suggestion:{}", line),
            description: format!("did you mean `{}`?", best_name),
            replacements: vec![Replacement {
                file: file.to_string(),
                span: Span::new(byte_start, byte_end, line, column),
                new_text: best_name.to_string(),
            }],
            confidence: FixConfidence::Likely,
        })
    } else {
        None
    }
}

/// Suggest a type coercion fix for a type mismatch.
///
/// Returns an EasyFix inserting the appropriate conversion method.
pub fn suggest_type_coercion_fix(
    file: &str,
    line: usize,
    column: usize,
    byte_end: usize,
    expected_type: &str,
    actual_type: &str,
) -> Option<EasyFix> {
    let coercion = match (expected_type, actual_type) {
        ("String", "Int") | ("String", "Float") | ("String", "Bool") => ".to_string()",
        ("Int", "Float") => ".to_int()",
        ("Float", "Int") => ".to_float()",
        ("Bool", "Int") => " != 0",
        _ => return None,
    };

    Some(EasyFix {
        id: format!("E:type_mismatch_coercion:{}", line),
        description: format!("insert `{}` to convert {} to {}", coercion, actual_type, expected_type),
        replacements: vec![Replacement {
            file: file.to_string(),
            span: Span::new(byte_end, byte_end, line, column),
            new_text: coercion.to_string(),
        }],
        confidence: FixConfidence::Likely,
    })
}

/// Suggest a keyword reorder fix for parser contextual keyword errors.
///
/// Detects common misordered keyword sequences and returns the correct order.
pub fn suggest_keyword_reorder(
    file: &str,
    line: usize,
    column: usize,
    byte_start: usize,
    found_keywords: &str,
) -> Option<EasyFix> {
    let (correct, old_len) = match found_keywords {
        "async static fn " => ("static async fn ", 16),
        "static pub fn " => ("pub static fn ", 14),
        "pub async static fn " => ("pub static async fn ", 20),
        _ => return None,
    };

    Some(EasyFix {
        id: format!("E:parser_contextual_keyword:{}", line),
        description: format!("reorder keywords: `{}`", correct.trim()),
        replacements: vec![Replacement {
            file: file.to_string(),
            span: Span::new(byte_start, byte_start + old_len, line, column),
            new_text: correct.to_string(),
        }],
        confidence: FixConfidence::Safe,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // ================================================================
    // Levenshtein distance tests
    // ================================================================

    #[test]
    fn test_levenshtein_identical() {
        assert_eq!(levenshtein("hello", "hello"), 0);
    }

    #[test]
    fn test_levenshtein_empty() {
        assert_eq!(levenshtein("", "abc"), 3);
        assert_eq!(levenshtein("abc", ""), 3);
        assert_eq!(levenshtein("", ""), 0);
    }

    #[test]
    fn test_levenshtein_single_edit() {
        assert_eq!(levenshtein("helo", "hello"), 1);  // insertion
        assert_eq!(levenshtein("hello", "helo"), 1);   // deletion
        assert_eq!(levenshtein("hello", "hallo"), 1);  // substitution
    }

    #[test]
    fn test_levenshtein_two_edits() {
        assert_eq!(levenshtein("kitten", "sittin"), 2);
    }

    #[test]
    fn test_levenshtein_completely_different() {
        assert_eq!(levenshtein("abc", "xyz"), 3);
    }

    // ================================================================
    // Typo suggestion tests
    // ================================================================

    #[test]
    fn test_suggest_typo_close_match() {
        let known = vec!["println", "print", "format"];
        let fix = suggest_typo_fix("test.spl", 1, 1, 0, 4, "prnt", &known);
        assert!(fix.is_some());
        let fix = fix.unwrap();
        assert_eq!(fix.replacements[0].new_text, "print");
        assert_eq!(fix.confidence, FixConfidence::Likely);
    }

    #[test]
    fn test_suggest_typo_no_match() {
        let known = vec!["println", "print", "format"];
        let fix = suggest_typo_fix("test.spl", 1, 1, 0, 9, "xyzxyzxyz", &known);
        assert!(fix.is_none());
    }

    #[test]
    fn test_suggest_typo_picks_closest() {
        let known = vec!["print", "println", "printf"];
        let fix = suggest_typo_fix("test.spl", 1, 1, 0, 4, "prnt", &known);
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, "print");
    }

    // ================================================================
    // Type coercion tests
    // ================================================================

    #[test]
    fn test_coercion_int_to_string() {
        let fix = suggest_type_coercion_fix("t.spl", 1, 10, 15, "String", "Int");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, ".to_string()");
    }

    #[test]
    fn test_coercion_float_to_int() {
        let fix = suggest_type_coercion_fix("t.spl", 1, 10, 15, "Int", "Float");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, ".to_int()");
    }

    #[test]
    fn test_coercion_int_to_float() {
        let fix = suggest_type_coercion_fix("t.spl", 1, 10, 15, "Float", "Int");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, ".to_float()");
    }

    #[test]
    fn test_coercion_int_to_bool() {
        let fix = suggest_type_coercion_fix("t.spl", 1, 10, 15, "Bool", "Int");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, " != 0");
    }

    #[test]
    fn test_coercion_unknown_types() {
        let fix = suggest_type_coercion_fix("t.spl", 1, 10, 15, "MyType", "Other");
        assert!(fix.is_none());
    }

    // ================================================================
    // Keyword reorder tests
    // ================================================================

    #[test]
    fn test_keyword_reorder_async_static() {
        let fix = suggest_keyword_reorder("t.spl", 1, 1, 0, "async static fn ");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, "static async fn ");
    }

    #[test]
    fn test_keyword_reorder_static_pub() {
        let fix = suggest_keyword_reorder("t.spl", 1, 1, 0, "static pub fn ");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, "pub static fn ");
    }

    #[test]
    fn test_keyword_reorder_pub_async_static() {
        let fix = suggest_keyword_reorder("t.spl", 1, 1, 0, "pub async static fn ");
        assert!(fix.is_some());
        assert_eq!(fix.unwrap().replacements[0].new_text, "pub static async fn ");
    }

    #[test]
    fn test_keyword_reorder_correct_order() {
        let fix = suggest_keyword_reorder("t.spl", 1, 1, 0, "static async fn ");
        assert!(fix.is_none());
    }
}
