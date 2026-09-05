//! Regression tests for struct-update spread `..base`.
//!
//! Bug: `doc/08_tracking/bug/struct_spread_paren_form_parses_as_range_2026-08-30.md`.
//! PAREN-form spread (`MirFunction(..function, blocks: blocks)`) used to fall
//! into `parse_range` and produce `Expr::Range { start: None, end }`, which
//! lowers to `rt_range(0, <tagged object pointer>)` — billions of elements,
//! i.e. a compiler HANG. All 110 spread sites in `src/` use the paren form.
//!
//! The half of these tests that matters most is the second half: `..` is
//! shared with range syntax, and turning genuine ranges into spreads would be
//! far worse than the original bug.

use simple_parser::Parser;

fn ast_debug(src: &str) -> String {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("should parse");
    format!("{:?}", module.items)
}

fn assert_spread(src: &str) {
    let ast = ast_debug(src);
    assert!(ast.contains("StructSpread"), "expected a StructSpread node in: {ast}");
}

fn assert_no_spread(src: &str) {
    let ast = ast_debug(src);
    assert!(
        !ast.contains("StructSpread"),
        "expected NO StructSpread node (this must stay a range) in: {ast}"
    );
}

fn assert_range(src: &str) {
    let ast = ast_debug(src);
    assert!(ast.contains("Range {"), "expected a Range node in: {ast}");
    assert!(
        !ast.contains("StructSpread"),
        "a genuine range was misparsed as a struct spread: {ast}"
    );
}

// === paren form: the shape the whole tree actually uses ===

#[test]
fn paren_spread_first_position() {
    assert_spread("fn f():\n    val x = MirFunction(..function, blocks: blocks)\n");
}

#[test]
fn paren_spread_on_self() {
    // 45 of the 110 repo sites are exactly this shape.
    assert_spread("fn f():\n    val x = State(..self, count: 1)\n");
}

#[test]
fn paren_spread_last_position() {
    assert_spread("fn f():\n    val x = Point(x: 1, ..base)\n");
}

#[test]
fn paren_spread_middle_position() {
    assert_spread("fn f():\n    val x = Point(x: 1, ..base, y: 2)\n");
}

#[test]
fn paren_spread_only_argument() {
    assert_spread("fn f():\n    val x = Point(..base)\n");
}

#[test]
fn paren_spread_of_call_expression() {
    assert_spread("fn f():\n    val x = Point(..make_base(), y: 2)\n");
}

#[test]
fn paren_spread_of_field_path() {
    assert_spread("fn f():\n    val x = Point(..self.origin, y: 2)\n");
}

#[test]
fn paren_spread_multiline() {
    assert_spread("fn f():\n    val x = MirFunction(\n        ..function,\n        blocks: blocks,\n    )\n");
}

// === brace form: what the parser already half-supported ===

#[test]
fn brace_spread_still_parses() {
    // The brace form carries the base in `StructInit.spread`, not in a
    // `StructSpread` argument node — a different AST shape for the same
    // feature. HIR lowering routes both through `lower_struct_init_fields`.
    let ast = ast_debug("fn f():\n    val x = Point { x: 1, ..base }\n");
    assert!(
        ast.contains(r#"spread: Some(Identifier("base"))"#),
        "expected brace-form StructInit.spread in: {ast}"
    );
}

// === ranges must still be ranges — the regression that would matter most ===

#[test]
fn binary_range_unaffected() {
    assert_range("fn f():\n    val r = a..b\n");
    assert_range("fn f():\n    val r = 0..n\n");
    assert_range("fn f():\n    val r = 0..=n\n");
}

#[test]
fn range_as_call_argument_is_still_a_range() {
    // `f(1..5)` does not START with `..`, so it never reaches the spread rule.
    assert_range("fn f():\n    take(1..5)\n");
    assert_range("fn f():\n    take(a..b)\n");
}

#[test]
fn for_loop_range_unaffected() {
    assert_range("fn f():\n    for i in 0..n:\n        pass\n");
}

#[test]
fn index_prefix_range_unaffected() {
    // Bracket-position prefix ranges never go through `parse_arguments`.
    assert_no_spread("fn f():\n    val s = arr[..n]\n");
    assert_no_spread("fn f():\n    val s = arr[a..b]\n");
    assert_no_spread("fn f():\n    val s = arr[n..]\n");
}

#[test]
fn suffix_range_unaffected() {
    assert_range("fn f():\n    val r = offset..\n");
}

#[test]
fn full_range_argument_is_not_a_spread() {
    // `f(..)` — `..` immediately followed by `)` cannot start an expression,
    // so the spread rule must not fire and `parse_range` still handles it.
    assert_no_spread("fn f():\n    take(..)\n");
}

#[test]
fn inclusive_prefix_range_argument_is_not_a_spread() {
    // `..=x` is a distinct token (`DoubleDotEq`); the spread rule only ever
    // looks at `DoubleDot`.
    assert_no_spread("fn f():\n    take(..=x)\n");
}
