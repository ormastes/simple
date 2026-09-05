//! Regression: `|` or-patterns inside an enum payload sub-pattern must parse.
//! Before this, `case Shape.Square(2 | 3):` failed with
//! "Unexpected token: expected Comma, found Pipe", while ranges
//! (`case Shape.Square(1..5):`) already worked. Commas inside the payload stay
//! structural slot separators — they must never build an Or.

use simple_parser::Parser;

fn parse_result(src: &str) -> Result<(), String> {
    let mut parser = Parser::new(src);
    parser.parse().map(|_| ()).map_err(|e| format!("{:?}", e))
}

fn parse_ok(src: &str, what: &str) {
    if let Err(e) = parse_result(src) {
        panic!("{what} must parse, got: {e}");
    }
}

#[test]
fn or_literals_in_payload_parses() {
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Square(2 | 3):\n            return 1\n        case _:\n            return 0\n",
        "or-literals in a payload",
    );
}

#[test]
fn or_over_nested_enums_with_shared_binder_parses() {
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Wrap(Inner.A(n) | Inner.B(n)):\n            return n\n        case _:\n            return 0\n",
        "or over nested enums with a shared binder",
    );
}

#[test]
fn or_combined_with_range_in_payload_parses() {
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Square(1..5 | 9):\n            return 1\n        case Shape.Square(0 | 20..30):\n            return 2\n        case _:\n            return 0\n",
        "or combined with ranges",
    );
}

#[test]
fn multi_slot_payload_with_or_in_each_slot_parses() {
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Rect(1 | 2, 3 | 4):\n            return 1\n        case Shape.Rect(w, 5 | 6):\n            return w\n        case _:\n            return 0\n",
        "multi-slot payload with or in each slot",
    );
}

#[test]
fn nested_payload_or_inside_inner_variant_parses() {
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Wrap(Inner.A(1 | 2 | 3)):\n            return 1\n        case _:\n            return 0\n",
        "nested payload with or inside the inner variant",
    );
}

#[test]
fn named_field_payload_slot_accepts_or() {
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Square(side: 2 | 3):\n            return 1\n        case _:\n            return 0\n",
        "named-field payload slot with or",
    );
}

#[test]
fn payload_commas_still_separate_slots_not_or() {
    // Two slots, not a 2-alternative Or: a wrong-arity payload would be a
    // semantic error, but parsing must keep the comma structural.
    parse_ok(
        "fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Rect(a, b):\n            return a + b\n        case _:\n            return 0\n",
        "commas as slot separators",
    );
}
