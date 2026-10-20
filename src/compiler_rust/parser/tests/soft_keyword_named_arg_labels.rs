//! Soft keywords as named-argument labels in calls and constructors.
//!
//! Bug: `S(flat: 1, base: 2)` failed with "expected Comma, found Colon".
//! `base` is a plain identifier; `flat` lexes as `TokenKind::Flat`, which the
//! named-argument label allow-list in `expressions/helpers.rs` did not list.
//! The same hole existed for the other soft keywords that are already legal
//! field names: slice, common, comptime, newtype, bitfield, extend, asm, out_err.

use simple_parser::Parser;

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    if let Err(err) = parser.parse() {
        panic!("should parse, got error: {err}\n--- source ---\n{src}");
    }
}

fn parse_err(src: &str) {
    let mut parser = Parser::new(src);
    assert!(parser.parse().is_ok() == false, "should NOT parse:\n{src}");
}

#[test]
fn flat_and_base_are_named_arg_labels() {
    parse_ok("struct S:\n    flat: i64\n    base: i64\nval s = S(flat: 1, base: 2)\n");
    parse_ok("struct S:\n    flat: i64\n    base: i64\nval s = S(flat = 1, base = 2)\n");
    parse_ok("fn f(flat: i64, base: i64) -> i64:\n    flat + base\nval r = f(base: 2, flat: 1)\n");
}

#[test]
fn every_soft_keyword_is_a_named_arg_label() {
    for kw in [
        "flat", "slice", "common", "comptime", "newtype", "bitfield", "extend", "asm", "out_err",
    ] {
        parse_ok(&format!("struct S:\n    {kw}: i64\nval s = S({kw}: 1)\n"));
        parse_ok(&format!("val s = S(a: 0, {kw}: 1)\n"));
    }
}

/// Negative: hard keywords are still not argument labels.
#[test]
fn hard_keywords_are_still_rejected_as_labels() {
    for kw in ["fn", "struct", "enum", "trait"] {
        parse_err(&format!("val s = S({kw}: 1)\n"));
    }
}

/// Negative: `flat` / `slice` remain real keywords in a tensor literal.
#[test]
fn flat_and_slice_still_work_as_tensor_mode_keywords() {
    parse_ok("val t = tensor K: Float [d=2, w=2]\n    flat:\n        | 1 | 2 |\n        | 3 | 4 |\n");
    parse_ok("val t = tensor K: Float [d=2, w=2]\n    default: 0\n    flat:\n        | 1 | 2 |\n        | 3 | 4 |\n");
}

/// Negative: a bare `flat` expression (no colon) still parses as a value.
#[test]
fn flat_as_plain_value_argument() {
    parse_ok("val flat = 3\nval r = f(flat)\nval q = f(a: flat)\n");
}
