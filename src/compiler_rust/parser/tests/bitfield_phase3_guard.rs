//! B4-sugar Phase 3: parser-level regression tests for the side-effecting
//! receiver guard and for the defer-body desugar.
//!
//! These tests pin the diagnostic that `parse_expression_or_assignment` and
//! `parse_defer_body` emit when the bitfield write target has a side-
//! effecting subexpression on its lvalue spine. The desugar duplicates the
//! lvalue 2-3 times, so calls/methods on the spine would re-execute their
//! side effects. Phase 3 ships diagnose-only — full single-eval temp
//! binding is deferred. These tests prevent a future change from silently
//! removing the guard.
//!
//! Three call sites have slightly different diagnostic strings; each is
//! pinned independently:
//! 1. `parse_expression_or_assignment` plain `=` path.
//! 2. `parse_expression_or_assignment` augmented `+=` path.
//! 3. `parse_defer_body` single-line `defer x.bits[…] = v` path.
//!
//! Positive tests pin that pure lvalues (literal/identifier indices) still
//! desugar successfully — i.e. the predicate's allow-list isn't too tight.

use simple_parser::error::ParseError;
use simple_parser::Parser;

/// Helper: parse a snippet and return the error if any.
fn parse_err(src: &str) -> Option<ParseError> {
    let mut parser = Parser::new(src);
    parser.parse().err()
}

/// Helper: assert parsing fails with a SyntaxError whose message contains
/// the expected substring.
fn assert_syntax_error_contains(src: &str, needle: &str) {
    let err = parse_err(src).unwrap_or_else(|| {
        panic!(
            "expected parse error containing {needle:?}, but parse succeeded for:\n{src}"
        )
    });
    let msg = match &err {
        ParseError::SyntaxError { message, .. } => message.clone(),
        other => format!("{other:?}"),
    };
    assert!(
        msg.contains(needle),
        "expected error message to contain {needle:?}, got:\n{msg}"
    );
}

// ---- Side-effect guard: plain `=` ------------------------------------------

#[test]
fn phase3_rejects_call_on_lvalue_spine_in_plain_assign() {
    let src = r#"
fn next_idx() -> Int:
    return 0

fn run():
    var arr = [0, 0]
    arr[next_idx()].bits[0..8] = 0x42
"#;
    assert_syntax_error_contains(src, "bind to a temp first");
}

#[test]
fn phase3_rejects_method_call_receiver_in_plain_assign() {
    // Method call on the lvalue spine — `obj.next().bits[…] = v`.
    let src = r#"
fn run():
    var obj = SomeObj()
    obj.next().bits[0..8] = 0x42
"#;
    assert_syntax_error_contains(src, "bind to a temp first");
}

// ---- Side-effect guard: augmented `+=` -------------------------------------

#[test]
fn phase3_rejects_call_on_lvalue_spine_in_augmented_assign() {
    let src = r#"
fn next_idx() -> Int:
    return 0

fn run():
    var arr = [0, 0]
    arr[next_idx()].bits[0..8] += 0x05
"#;
    assert_syntax_error_contains(src, "bind to a temp first");
}

// ---- Side-effect guard: defer-body single-line write -----------------------

#[test]
fn phase3_rejects_call_on_lvalue_spine_in_defer_body() {
    let src = r#"
fn next_idx() -> Int:
    return 0

fn run():
    var arr = [0, 0]
    defer arr[next_idx()].bits[0..8] = 0x42
"#;
    assert_syntax_error_contains(src, "in defer body");
}

// ---- Positive cases: pure lvalues still desugar OK -------------------------

#[test]
fn phase3_accepts_literal_index_in_plain_assign() {
    let src = r#"
fn run():
    var arr = [0, 0]
    arr[0].bits[0..8] = 0x42
"#;
    let mut parser = Parser::new(src);
    let result = parser.parse();
    assert!(
        result.is_ok(),
        "expected parse to succeed for pure literal index, got: {:?}",
        result.err()
    );
}

#[test]
fn phase3_accepts_identifier_index_in_plain_assign() {
    let src = r#"
fn run():
    var arr = [0, 0]
    var i = 1
    arr[i].bits[0..8] = 0x42
"#;
    let mut parser = Parser::new(src);
    let result = parser.parse();
    assert!(
        result.is_ok(),
        "expected parse to succeed for pure identifier index, got: {:?}",
        result.err()
    );
}

#[test]
fn phase3_accepts_plain_identifier_in_plain_assign() {
    let src = r#"
fn run():
    var state = 0
    state.bits[0..8] = 0x42
"#;
    let mut parser = Parser::new(src);
    let result = parser.parse();
    assert!(
        result.is_ok(),
        "expected parse to succeed for plain identifier, got: {:?}",
        result.err()
    );
}

#[test]
fn phase3_accepts_defer_body_with_pure_lvalue() {
    // The Phase 3 fix: this used to leave a raw FieldAccess("bits") in
    // the AST. Verify it now desugars (parses cleanly) inside defer too.
    let src = r#"
fn run():
    var state = 0
    defer state.bits[0..8] = 0x42
"#;
    let mut parser = Parser::new(src);
    let result = parser.parse();
    assert!(
        result.is_ok(),
        "expected parse to succeed for defer-body pure lvalue, got: {:?}",
        result.err()
    );
}
