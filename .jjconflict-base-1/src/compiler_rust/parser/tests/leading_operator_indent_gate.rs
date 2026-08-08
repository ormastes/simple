// Regression gate for
// doc/08_tracking/bug/if_chain_last_arm_returns_previous_value_2026-07-28.md
//
// A statement-leading `-`/`+` at the SAME indent as the previous statement must
// stay a separate statement. Before the fix, `parse_term`'s "Case 2"
// leading-operator continuation peeked through NEWLINE/INDENT without ever
// consulting indentation, so
//
//     fn f() -> i64:
//         15
//         -1
//
// parsed as `15 - 1` (one statement, value 14) instead of two statements
// (value -1). The fix is the `indent_required` variant of `parse_binary_multi!`
// (expressions/binary.rs) backed by `peek_indented_operator_continuation`
// (parser_helpers.rs), which only takes the continuation when at least one
// `Indent` token was crossed.
//
// The DEEPER-indented form is a real, intended continuation and must keep
// working — the `keeps_*` cases pin that so the fix cannot over-correct.
//
// Run: cargo test -p simple-parser --test leading_operator_indent_gate

fn debug_ast(src: &str) -> String {
    let module = simple_parser::Parser::new(src)
        .parse()
        .unwrap_or_else(|e| panic!("parse failed for:\n{src}\nerror: {e:?}"));
    format!("{module:?}")
}

fn assert_no_binop(src: &str, op: &str, what: &str) {
    let ast = debug_ast(src);
    assert!(
        !ast.contains(op),
        "{what}: same-indent leading operator was glued into a binary `{op}`.\n\
         source:\n{src}\nast:\n{ast}"
    );
}

fn assert_has_binop(src: &str, op: &str, what: &str) {
    let ast = debug_ast(src);
    assert!(
        ast.contains(op),
        "{what}: deeper-indented leading operator lost its continuation \
         (expected a binary `{op}`).\nsource:\n{src}\nast:\n{ast}"
    );
}

#[test]
fn same_indent_leading_minus_is_a_separate_statement() {
    // The pure form from the bug report: no `if`, no chain.
    assert_no_binop("fn f() -> i64:\n    15\n    -1\n", "Sub", "pure form");
}

#[test]
fn same_indent_leading_plus_no_longer_glues_silently() {
    // There is no unary-prefix `+`, so a bare `+1` statement has no valid
    // parse. Before the fix it was silently absorbed as `15 + 1` (= 16); now it
    // is a hard parse error. A diagnostic is the acceptable outcome here — the
    // defect being fixed is the SILENT wrong arithmetic.
    let src = "fn f() -> i64:\n    15\n    +1\n";
    assert!(
        simple_parser::Parser::new(src).parse().is_err(),
        "same-indent leading `+` must not silently glue into `15 + 1`"
    );
}

#[test]
fn same_indent_leading_minus_after_single_line_if_is_a_separate_statement() {
    // The originally reported hex-nibble decoder shape.
    assert_no_binop(
        "fn hex_digit(c: text) -> i64:\n    if c == \"f\": return 15\n    -1\n",
        "Sub",
        "single-line if + `-1` sentinel tail",
    );
}

#[test]
fn a_blank_line_does_not_re_enable_the_same_indent_glue() {
    assert_no_binop(
        "fn f(c: text) -> i64:\n    if c == \"f\": return 15\n\n    -1\n",
        "Sub",
        "blank line between the two statements",
    );
}

#[test]
fn same_indent_leading_minus_after_an_assignment_is_a_separate_statement() {
    assert_no_binop(
        "fn f(c: text) -> i64:\n    var r = 0\n    if c == \"f\": r = 15\n    -1\n    return r\n",
        "Sub",
        "assignment-style arm",
    );
}

#[test]
fn keeps_deeper_indented_leading_minus_as_a_continuation() {
    assert_has_binop(
        "fn f() -> i64:\n    val s = 10\n        - 5\n    return s\n",
        "Sub",
        "deeper-indented `- 5`",
    );
}

#[test]
fn keeps_deeper_indented_leading_plus_as_a_continuation() {
    assert_has_binop(
        "fn f() -> i64:\n    val s = 10\n        + 5\n    return s\n",
        "Add",
        "deeper-indented `+ 5`",
    );
}

#[test]
fn keeps_deeper_indented_leading_plus_builder_chain() {
    // The `+ RB()` JSON-builder chains in src/app/mcpgdb/** and
    // src/app/serial_mcp/main.spl are deeper-indented continuations and must
    // survive the fix.
    assert_has_binop(
        "fn body() -> text:\n    return lb()\n        + jp(\"a\")\n        + \",\"\n        + rb()\n",
        "Add",
        "builder chain",
    );
}

#[test]
fn keeps_trailing_operator_continuation() {
    // Case 1 (trailing operator) is untouched by the fix.
    assert_has_binop(
        "fn f(a: i64, b: i64) -> i64:\n    val x = a +\n       b\n    return x\n",
        "Add",
        "trailing `+`",
    );
}
