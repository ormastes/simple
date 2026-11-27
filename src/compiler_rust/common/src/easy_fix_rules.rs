//! EasyFix Rules — thin bridge to Simple implementation
//!
//! Instead of duplicating rule logic in Rust, this module provides:
//! 1. A bridge to call the Simple rules (`src/app/fix/rules.spl`) via the interpreter SFFI
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
            curr[j] = (prev[j] + 1).min(curr[j - 1] + 1).min(prev[j - 1] + cost);
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

// ============================================================================
// W-STR-BRACE-001: literal braces in string literals -> `{{` / `}}` escapes
// (parity port of the pure-Simple rule compiler.tools.fix.rules.impl_.
// lint_str_brace; see that module's header for the full variant list and the
// deliberately-conservative negative cases)
// ============================================================================

/// One flagged brace site: replace `source[start..end]` with `new_text`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrBraceSite {
    pub start: usize,
    pub end: usize,
    pub new_text: String,
}

/// Custom-block `kind{...}` openers whose raw payload never warns.
const STR_BRACE_BLOCK_KINDS: [&str; 14] = [
    "m", "sh", "sql", "schema", "style", "re", "rtl", "md", "music", "html", "graph", "img", "ui",
    "pc",
];

/// Bytes that can never begin a Simple expression (`|` excluded: it opens a
/// `|x| body` lambda, a valid interpolation).
const STR_BRACE_INVALID_START: &[u8] = b";=<>?,)]#";

/// Scan source text for W-STR-BRACE-001 sites (seed-lexer warn_brace parity).
///
/// Returns byte-offset sites in ascending order. Behavior-preserving: every
/// flagged brace was already kept as literal text by the lexer, and the
/// doubled-brace escape decodes back to the same text.
pub fn scan_str_brace_sites(source: &str) -> Vec<StrBraceSite> {
    let mut sites = Vec::new();
    let mut offset = 0usize;
    let mut in_triple = false;
    for line in source.split('\n') {
        let bytes = line.as_bytes();
        let start = if in_triple {
            match str_brace_find_triple_end(bytes, 0) {
                Some(close) => {
                    in_triple = false;
                    close + 3
                }
                None => {
                    offset += line.len() + 1;
                    continue;
                }
            }
        } else {
            0
        };
        str_brace_scan_code_line(bytes, start, offset, &mut sites);
        if !in_triple {
            in_triple = str_brace_line_opens_triple(bytes);
        }
        offset += line.len() + 1;
    }
    sites
}

/// Propose one EasyFix per flagged site of a source file.
pub fn suggest_str_brace_fixes(file: &str, source: &str) -> Vec<EasyFix> {
    scan_str_brace_sites(source)
        .iter()
        .map(|site| EasyFix {
            id: format!("W-STR-BRACE-001:{}", site.start),
            description: "escape literal brace in string literal with an explicit doubled-brace escape (W-STR-BRACE-001)".to_string(),
            replacements: vec![Replacement {
                file: file.to_string(),
                span: Span::new(site.start, site.end, 1, site.start + 1),
                new_text: site.new_text.clone(),
            }],
            confidence: FixConfidence::Safe,
        })
        .collect()
}

fn str_brace_is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn str_brace_is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn str_brace_at(bytes: &[u8], i: usize) -> u8 {
    if i < bytes.len() {
        bytes[i]
    } else {
        0
    }
}

fn str_brace_find_triple_end(bytes: &[u8], mut j: usize) -> Option<usize> {
    while j + 3 <= bytes.len() {
        if &bytes[j..j + 3] == b"\"\"\"" {
            return Some(j);
        }
        j += 1;
    }
    None
}

fn str_brace_skip_raw_string(bytes: &[u8], mut j: usize) -> usize {
    while j < bytes.len() {
        if bytes[j] == b'"' {
            return j + 1;
        }
        j += 1;
    }
    bytes.len()
}

fn str_brace_skip_single_quoted(bytes: &[u8], start: usize) -> usize {
    let mut j = start + 1;
    while j < bytes.len() {
        match bytes[j] {
            b'\\' => j += 2,
            b'\'' => return j + 1,
            _ => j += 1,
        }
    }
    start + 1
}

fn str_brace_skip_block_payload(bytes: &[u8], open_idx: usize) -> usize {
    let mut depth = 1i32;
    let mut k = open_idx + 1;
    while k < bytes.len() {
        match bytes[k] {
            b'\\' => k += 2,
            b'"' => {
                k = str_brace_skip_raw_string(bytes, k);
            }
            b'{' => {
                depth += 1;
                k += 1;
            }
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return k + 1;
                }
                k += 1;
            }
            _ => k += 1,
        }
    }
    bytes.len()
}

/// Scan one line of code for string literals and flag brace sites inside.
fn str_brace_scan_code_line(bytes: &[u8], start: usize, offset: usize, sites: &mut Vec<StrBraceSite>) {
    let mut i = start;
    while i < bytes.len() {
        match bytes[i] {
            b'#' => break,
            b'\\' => i += 2,
            b'\'' => {
                i = str_brace_skip_single_quoted(bytes, i);
            }
            b'"' => {
                if i + 3 <= bytes.len() && &bytes[i..i + 3] == b"\"\"\"" {
                    break;
                }
                let (line_sites, next) = str_brace_scan_interp_string(bytes, i + 1);
                for site in line_sites {
                    sites.push(StrBraceSite {
                        start: offset + site.start,
                        end: offset + site.end,
                        new_text: site.new_text,
                    });
                }
                i = next;
            }
            b'f' | b'r'
                if i == 0 || !str_brace_is_ident_char(bytes[i - 1]) =>
            {
                if str_brace_at(bytes, i + 1) == b'"' {
                    if i + 4 <= bytes.len() && &bytes[i + 1..i + 4] == b"\"\"\"" {
                        break;
                    }
                    if bytes[i] == b'r' {
                        i = str_brace_skip_raw_string(bytes, i + 2);
                    } else {
                        let (line_sites, next) = str_brace_scan_interp_string(bytes, i + 2);
                        for site in line_sites {
                            sites.push(StrBraceSite {
                                start: offset + site.start,
                                end: offset + site.end,
                                new_text: site.new_text,
                            });
                        }
                        i = next;
                    }
                } else {
                    i = str_brace_skip_identifier_or_block(bytes, i);
                }
            }
            b if str_brace_is_ident_start(b) => {
                i = str_brace_skip_identifier_or_block(bytes, i);
            }
            _ => i += 1,
        }
    }
}

fn str_brace_skip_identifier_or_block(bytes: &[u8], start: usize) -> usize {
    let mut j = start;
    while j < bytes.len() && str_brace_is_ident_char(bytes[j]) {
        j += 1;
    }
    if j < bytes.len() && bytes[j] == b'{' {
        let ident = &bytes[start..j];
        if STR_BRACE_BLOCK_KINDS.iter().any(|kind| ident == kind.as_bytes()) {
            return str_brace_skip_block_payload(bytes, j);
        }
    }
    j
}

/// Scan an interpolated string's content after the opening quote; returns
/// (sites with line-relative offsets, index after the closing quote or EOL).
fn str_brace_scan_interp_string(bytes: &[u8], content_start: usize) -> (Vec<StrBraceSite>, usize) {
    let mut sites = Vec::new();
    let mut j = content_start;
    while j < bytes.len() {
        match bytes[j] {
            b'\\' => j += 2,
            b'"' => return (sites, j + 1),
            b'{' => {
                let next = str_brace_at(bytes, j + 1);
                if next == b'{' {
                    j += 2;
                } else if next == 0 || next == b'\\' || next == b'\'' || next == b'"' {
                    sites.push(StrBraceSite {
                        start: j,
                        end: j + 1,
                        new_text: "{{".to_string(),
                    });
                    j += 1;
                } else if next == b'}' {
                    sites.push(StrBraceSite {
                        start: j,
                        end: j + 2,
                        new_text: "{{}}".to_string(),
                    });
                    j += 2;
                } else {
                    let (region_sites, resume, stop) = str_brace_scan_region(bytes, j);
                    sites.extend(region_sites);
                    if stop {
                        return (sites, resume);
                    }
                    j = resume;
                }
            }
            b'}' => {
                if str_brace_at(bytes, j + 1) == b'}' {
                    j += 2;
                } else {
                    j += 1;
                }
            }
            _ => j += 1,
        }
    }
    (sites, bytes.len())
}

/// Scan a `{` region (first char known not to be `{`, `}`, escape, or quote).
fn str_brace_scan_region(bytes: &[u8], open_idx: usize) -> (Vec<StrBraceSite>, usize, bool) {
    let mut depth = 1i32;
    let mut k = open_idx + 1;
    let mut in_str = 0u8;
    while k < bytes.len() {
        let ch = bytes[k];
        if ch == b'\\' {
            k += 2;
            continue;
        }
        if in_str != 0 {
            if ch == in_str {
                in_str = 0;
            }
            k += 1;
            continue;
        }
        match ch {
            b'"' => {
                if !str_brace_operand_expected(&bytes[open_idx + 1..k]) {
                    return (
                        vec![StrBraceSite {
                            start: open_idx,
                            end: open_idx + 1,
                            new_text: "{{".to_string(),
                        }],
                        k,
                        true,
                    );
                }
                in_str = b'"';
                k += 1;
            }
            b'\'' => {
                let prev = bytes[k - 1];
                if str_brace_is_ident_char(prev) || prev == b')' {
                    k += 1;
                } else {
                    in_str = b'\'';
                    k += 1;
                }
            }
            b'{' => {
                depth += 1;
                k += 1;
            }
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
                k += 1;
            }
            _ => k += 1,
        }
    }
    if depth != 0 {
        return (
            vec![StrBraceSite {
                start: open_idx,
                end: open_idx + 1,
                new_text: "{{".to_string(),
            }],
            k,
            true,
        );
    }
    let expr = &bytes[open_idx + 1..k];
    let expr_trimmed: &[u8] = {
        let mut a = 0;
        let mut b = expr.len();
        while a < b && (expr[a] == b' ' || expr[a] == b'\t') {
            a += 1;
        }
        while b > a && (expr[b - 1] == b' ' || expr[b - 1] == b'\t') {
            b -= 1;
        }
        &expr[a..b]
    };
    if expr_trimmed.is_empty() {
        // Both engines collapse a whitespace-only region's value to "{}".
        return (
            vec![StrBraceSite {
                start: open_idx,
                end: k + 1,
                new_text: "{{}}".to_string(),
            }],
            k + 1,
            false,
        );
    }
    if str_brace_region_definitely_malformed(expr) {
        let mut new_text = String::with_capacity(k + 1 - open_idx + 2);
        for &b in &bytes[open_idx..k + 1] {
            if b == b'{' || b == b'}' {
                new_text.push(b as char);
                new_text.push(b as char);
            } else {
                new_text.push(b as char);
            }
        }
        return (
            vec![StrBraceSite {
                start: open_idx,
                end: k + 1,
                new_text,
            }],
            k + 1,
            false,
        );
    }
    (Vec::new(), k + 1, false)
}

fn str_brace_region_definitely_malformed(expr: &[u8]) -> bool {
    let mut a = 0;
    let mut b = expr.len();
    while a < b && (expr[a] == b' ' || expr[a] == b'\t') {
        a += 1;
    }
    while b > a && (expr[b - 1] == b' ' || expr[b - 1] == b'\t') {
        b -= 1;
    }
    let trimmed = &expr[a..b];
    if trimmed.is_empty() {
        return false;
    }
    if STR_BRACE_INVALID_START.contains(&trimmed[0]) {
        return true;
    }
    let mut prev_nonws = 0u8;
    for (idx, &ch) in trimmed.iter().enumerate() {
        if ch == b'$' && idx > 0 {
            let after_operand = str_brace_is_ident_char(prev_nonws)
                || prev_nonws == b')'
                || prev_nonws == b']'
                || prev_nonws == b'}'
                || prev_nonws == b'"'
                || prev_nonws == b'\'';
            if after_operand {
                return true;
            }
        }
        if ch != b' ' && ch != b'\t' {
            prev_nonws = ch;
        }
    }
    false
}

fn str_brace_operand_expected(expr_so_far: &[u8]) -> bool {
    let mut a = 0;
    let mut b = expr_so_far.len();
    while a < b && (expr_so_far[a] == b' ' || expr_so_far[a] == b'\t') {
        a += 1;
    }
    while b > a && (expr_so_far[b - 1] == b' ' || expr_so_far[b - 1] == b'\t') {
        b -= 1;
    }
    let trimmed = &expr_so_far[a..b];
    if trimmed.is_empty() {
        return false;
    }
    for word in ["if", "else", "match"] {
        if str_brace_has_word(trimmed, word) {
            return true;
        }
    }
    for op in ["==", "!=", "<=", ">=", "??"] {
        if trimmed.ends_with(op.as_bytes()) {
            return true;
        }
    }
    let last = trimmed[trimmed.len() - 1];
    if matches!(last, b'<' | b'>' | b'+' | b'-' | b'*' | b'/' | b'%' | b',' | b'(' | b'[') {
        return true;
    }
    for kw in ["and", "or", "not", "in"] {
        if trimmed.ends_with(kw.as_bytes()) {
            let head = &trimmed[..trimmed.len() - kw.len()];
            if head.is_empty() || !str_brace_is_ident_char(head[head.len() - 1]) {
                return true;
            }
        }
    }
    false
}

fn str_brace_has_word(text: &[u8], word: &str) -> bool {
    let word = word.as_bytes();
    if word.len() > text.len() {
        return false;
    }
    let mut from = 0;
    while from + word.len() <= text.len() {
        let mut start = None;
        for i in from..=(text.len() - word.len()) {
            if &text[i..i + word.len()] == word {
                start = Some(i);
                break;
            }
        }
        let start = match start {
            Some(s) => s,
            None => return false,
        };
        let end = start + word.len();
        let before_ok = start == 0 || !str_brace_is_ident_char(text[start - 1]);
        let after_ok = end == text.len() || !str_brace_is_ident_char(text[end]);
        if before_ok && after_ok {
            return true;
        }
        from = start + 1;
    }
    false
}

fn str_brace_line_opens_triple(bytes: &[u8]) -> bool {
    let mut j = 0;
    let mut in_str = false;
    while j < bytes.len() {
        let ch = bytes[j];
        if !in_str && ch == b'#' {
            return false;
        }
        if in_str {
            if ch == b'\\' {
                j += 2;
                continue;
            }
            if ch == b'"' {
                in_str = false;
            }
            j += 1;
            continue;
        }
        match ch {
            b'"' => {
                if j + 3 <= bytes.len() && &bytes[j..j + 3] == b"\"\"\"" {
                    match str_brace_find_triple_end(bytes, j + 3) {
                        None => return true,
                        Some(close) => {
                            j = close + 3;
                            continue;
                        }
                    }
                }
                in_str = true;
                j += 1;
            }
            b'\'' => {
                j = str_brace_skip_single_quoted(bytes, j);
            }
            _ => j += 1,
        }
    }
    false
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
        assert_eq!(levenshtein("helo", "hello"), 1); // insertion
        assert_eq!(levenshtein("hello", "helo"), 1); // deletion
        assert_eq!(levenshtein("hello", "hallo"), 1); // substitution
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

    // ================================================================
    // W-STR-BRACE-001 string-literal brace escape tests
    // (parity with the pure-Simple rule lint_str_brace and the shapes of
    // the lintC/lintD hand fixes)
    // ================================================================

    fn site_texts(source: &str) -> Vec<String> {
        scan_str_brace_sites(source)
            .iter()
            .map(|site| site.new_text.clone())
            .collect()
    }

    /// Apply sites in descending order (the applicator's order) and return
    /// the rewritten source.
    fn apply_sites(source: &str, sites: &[StrBraceSite]) -> String {
        let mut sorted: Vec<&StrBraceSite> = sites.iter().collect();
        sorted.sort_by_key(|site| std::cmp::Reverse(site.start));
        let mut out = source.to_string();
        for site in sorted {
            out.replace_range(site.start..site.end, &site.new_text);
        }
        out
    }

    #[test]
    fn test_str_brace_quote_variant() {
        let sites = scan_str_brace_sites("val s = \"expected '{' after 'loss'\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{");
        assert_eq!(apply_sites("val s = \"expected '{' after 'loss'\"\n", &sites),
                   "val s = \"expected '{{' after 'loss'\"\n");
    }

    #[test]
    fn test_str_brace_escape_variant() {
        let sites = scan_str_brace_sites("val s = \"json: {\\\"key\\\": 1}\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{");
    }

    #[test]
    fn test_str_brace_empty_region() {
        let sites = scan_str_brace_sites("val s = \"m{} block\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{}}");
        assert_eq!(sites[0].end - sites[0].start, 2);
    }

    #[test]
    fn test_str_brace_whitespace_region_collapses() {
        // Both engines collapse a whitespace-only region's value to "{}",
        // so the fix emits the collapsed escape form over the whole region.
        let sites = scan_str_brace_sites("val s = \"m{   } block\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{}}");
        assert_eq!(sites[0].end - sites[0].start, 5);
    }

    #[test]
    fn test_str_brace_invalid_start_region() {
        let sites = scan_str_brace_sites("val s = \"sum {= 1} end\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{= 1}}");
    }

    #[test]
    fn test_str_brace_dollar_after_operand_region() {
        let sites = scan_str_brace_sites("val s = \"awk {print $1} end\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{print $1}}");
    }

    #[test]
    fn test_str_brace_unmatched_at_string_end() {
        let sites = scan_str_brace_sites("val s = \"prefix {\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{");
    }

    #[test]
    fn test_str_brace_concat_pattern() {
        // "\"{" + name + "}\"" — only the first literal's brace is flagged;
        // the later single close-brace literal is lenient and never warned.
        let sites = scan_str_brace_sites("val s = \"{\" + name + \"}\"\n");
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].new_text, "{{");
    }

    #[test]
    fn test_str_brace_skips_valid_interpolations() {
        let source = "fn f(name: text, x: i64) -> text:\n    val a = \"pre {name} post\"\n    val b = \"pad {x:>10} end\"\n    a + b\n";
        assert!(scan_str_brace_sites(source).is_empty());
    }

    #[test]
    fn test_str_brace_skips_pipe_lambda_interpolation() {
        // `|x| x + 1` is a valid lambda interpolation — never touch it.
        let source = "val s = \"closure {|x| x + 1} here\"\n";
        assert!(scan_str_brace_sites(source).is_empty());
    }

    #[test]
    fn test_str_brace_skips_already_escaped_and_backslash_escaped() {
        assert!(scan_str_brace_sites("val s = \"literal {{brace}} and {name}\"\n").is_empty());
        assert!(scan_str_brace_sites("val s = \"sed \\{0,1\\} here\"\n").is_empty());
    }

    #[test]
    fn test_str_brace_skips_raw_comment_and_block_payload() {
        let source = "# a comment with \"{ brace\nval a = r\"raw { brace\"\nval b = m{ print(\"{\") }\n";
        assert!(scan_str_brace_sites(source).is_empty());
    }

    #[test]
    fn test_str_brace_skips_triple_quoted() {
        let source = "fn doc() -> i64:\n    \"\"\"doc with { brace\n    and } more\"\"\"\n    0\n";
        assert!(scan_str_brace_sites(source).is_empty());
    }

    #[test]
    fn test_str_brace_byte_spans_are_source_relative() {
        let source = "val a = \"ok {name}\"\nval b = \"m{} x\"\n";
        let sites = scan_str_brace_sites(source);
        assert_eq!(sites.len(), 1);
        let brace_pos = "val a = \"ok {name}\"\n".len() + "val b = \"m".len();
        assert_eq!(sites[0].start, brace_pos);
        assert_eq!(sites[0].end, brace_pos + 2);
    }

    #[test]
    fn test_str_brace_idempotent_after_apply() {
        let source = "val s = \"m{} and {\\\"k\\\"} and {name}\"\n";
        let sites = scan_str_brace_sites(source);
        assert_eq!(sites.len(), 2);
        let rewritten = apply_sites(source, &sites);
        assert!(scan_str_brace_sites(&rewritten).is_empty());
    }

    #[test]
    fn test_suggest_str_brace_fixes_builds_safe_fixes() {
        let fixes = suggest_str_brace_fixes("t.spl", "val s = \"m{} x\"\n");
        assert_eq!(fixes.len(), 1);
        assert_eq!(fixes[0].confidence, FixConfidence::Safe);
        assert_eq!(fixes[0].replacements[0].file, "t.spl");
        assert_eq!(fixes[0].replacements[0].new_text, "{{}}");
    }
}
