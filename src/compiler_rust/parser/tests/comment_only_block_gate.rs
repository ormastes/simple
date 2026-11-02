//! Gate: a comment-only (or blank-gapped) block body must not let the next
//! sibling statement be swallowed as a "flat body".
//!
//! Bug: doc/08_tracking/bug/
//! comment_only_block_swallows_next_statement_2026-10-04.md
//! (pure-Simple fix: PR #5893; seed follow-up: lane p12-5).
//!
//! Comment/blank lines emit no Indent, so `if c:\n    # x\nstmt` looked like a
//! flat body (`stmt` at the header's column). A flat body is only legal on the
//! line immediately after the header.

use simple_parser::Parser;

fn parses(src: &str) -> bool {
    let mut p = Parser::new(src);
    p.parse().is_ok()
}

#[test]
fn comment_only_if_body_does_not_swallow_next_statement() {
    assert!(!parses("fn f():\n    if false:\n        # c\n    print(1)\n"));
}

#[test]
fn comment_only_top_level_if_body_is_an_error() {
    assert!(!parses("if false:\n    # c\nprint(1)\n"));
}

#[test]
fn blank_gap_flat_body_is_an_error() {
    assert!(!parses("if false:\n\nprint(1)\n"));
}

#[test]
fn comment_only_while_and_for_bodies_are_errors() {
    assert!(!parses("while false:\n    # c\nprint(1)\n"));
    assert!(!parses("for i in 0..1:\n    # c\nprint(1)\n"));
}

#[test]
fn flat_body_on_next_line_still_parses() {
    assert!(parses("fn f(x: i64):\n    if x > 0:\n    return 1\n    0\n"));
}

#[test]
fn normal_indented_body_with_leading_comment_parses() {
    assert!(parses("if true:\n    # c\n    print(1)\nprint(2)\n"));
}
