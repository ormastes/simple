//! Family sweep: where may a newline legally follow an operator/punctuator?
//!
//! Origin defect: `src/os/crypto/x25519_mlkem768/gpu_lifecycle_snapshot.spl`
//! wraps a function signature's return type onto the line after `->`, which the
//! parser rejected with "expected identifier, found Newline".  This file pins
//! the whole family so a sibling form cannot silently regress.

use simple_parser::error::ParseError;
use simple_parser::{ast::Module, Parser};

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
}

fn assert_parses(label: &str, source: &str) {
    if let Err(e) = parse(source) {
        panic!("{label}: expected to parse, got {e:?}\n--- source ---\n{source}");
    }
}

fn assert_rejects(label: &str, source: &str) {
    if parse(source).is_ok() {
        panic!("{label}: expected a parse ERROR, but it parsed\n--- source ---\n{source}");
    }
}

// === The reported defect: trailing `->`, return type on the next line ===

#[test]
fn fn_return_type_after_trailing_arrow_newline() {
    assert_parses(
        "trailing arrow, simple return type",
        "fn add_two(a: i64, b: i64) ->\n        i64:\n    a + b\n",
    );
}

#[test]
fn fn_return_type_after_trailing_arrow_generic() {
    // Exact shape from gpu_lifecycle_snapshot.spl: wrapped params AND a
    // generic return type on the line after the arrow.
    assert_parses(
        "trailing arrow, generic return type, wrapped params",
        "fn delta(\n        baseline: Snap,\n        current: Snap) ->\n        Result<Delta, text>:\n    Ok(1)\n",
    );
}

#[test]
fn fn_leading_arrow_on_next_line_still_parses() {
    // The pre-existing sibling form must not regress.
    assert_parses(
        "leading arrow on next line",
        "fn add_two(a: i64, b: i64)\n        -> i64:\n    a + b\n",
    );
}

#[test]
fn fn_normally_indented_body_after_wrapped_signature() {
    // Guards the indentation bookkeeping: the body must still bind at its own
    // level after the arrow continuation is drained.
    assert_parses(
        "wrapped signature then multi-statement body",
        "fn add_two(a: i64, b: i64) ->\n        i64:\n    val c = a + b\n    c\n",
    );
}

// === Must STILL be rejected: a parser that accepts everything is worse ===

#[test]
fn trailing_arrow_with_no_return_type_is_still_an_error() {
    assert_rejects(
        "trailing arrow, no type anywhere",
        "fn add_two(a: i64, b: i64) ->\n:\n    a + b\n",
    );
}

#[test]
fn trailing_arrow_at_eof_is_still_an_error() {
    assert_rejects("trailing arrow at EOF", "fn add_two(a: i64, b: i64) ->\n");
}

// === The rest of the family ===

#[test]
fn newline_after_binary_operator() {
    assert_parses(
        "trailing binary operator",
        "fn f(a: i64, b: i64) -> i64:\n    a +\n        b\n",
    );
}

#[test]
fn newline_after_boolean_operator() {
    assert_parses(
        "trailing `and`",
        "fn f(a: bool, b: bool) -> bool:\n    a and\n        b\n",
    );
}

#[test]
fn newline_after_comma_in_param_list() {
    assert_parses(
        "newline after `,` in params",
        "fn f(\n        a: i64,\n        b: i64) -> i64:\n    a + b\n",
    );
}

#[test]
fn newline_after_open_paren_in_call() {
    assert_parses(
        "newline after `(` in a call",
        "fn f(a: i64) -> i64:\n    a\nfn g() -> i64:\n    f(\n        1)\n",
    );
}

#[test]
fn newline_after_open_bracket_in_array_literal() {
    assert_parses("newline after `[`", "fn g() -> [i64]:\n    [\n        1,\n        2]\n");
}

#[test]
fn newline_inside_generic_argument_list() {
    assert_parses(
        "newline inside `<...>` return type",
        "fn g() -> Result<i64,\n        text>:\n    Ok(1)\n",
    );
}

#[test]
fn newline_after_arrow_in_closure_type_annotation() {
    assert_parses(
        "trailing arrow in a fn-type annotation",
        "fn g(cb: fn(i64) ->\n        i64) -> i64:\n    cb(1)\n",
    );
}

// Deliberately NOT tested here: `val f = (x: i64) -> x + 1`. That form fails
// *joined* too ("expected LParen, found Plus"), and the `=>` spelling fails
// joined and split identically ("expected expression, found FatArrow"), so
// neither is a newline defect -- a separate lambda-binding issue, out of scope
// for this file. Adding them here would have mislabeled a grammar gap as a
// continuation gap.

#[test]
fn newline_after_trailing_arrow_on_method() {
    assert_parses(
        "trailing arrow on a class method",
        "class C:\n    fn m(self, a: i64) ->\n            i64:\n        a\n",
    );
}

#[test]
fn newline_after_trailing_arrow_on_extern_fn() {
    assert_parses(
        "trailing arrow on an @extern fn",
        "@extern fn ex(a: i64) ->\n        i64\n",
    );
}
