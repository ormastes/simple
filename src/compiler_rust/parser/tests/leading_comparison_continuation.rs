// Regression gate for
// doc/08_tracking/bug/parser_leading_operator_line_continuation_2026-08-01.md
//
// The seed accepted a LEADING-operator line continuation
//
//     val x = a
//         + b
//
// for `+ - * / % & ^ << >> and or` but REJECTED it for the
// comparison/equality/membership/coalesce family `== != < > <= >= is in ??`,
// while the self-hosted parser accepted all of them. Cause: `parse_equality`
// and `parse_comparison` in `expressions/binary.rs` are hand-written (for
// `not in` and for `a < b < c` chaining respectively) and so never inherited
// the `parse_binary_*!` macros' "Case 2" leading-continuation arm — they only
// ever received the TRAILING-form fix from 023a60a05aa. `??` lives in
// `expressions/postfix.rs` and had the same gap.
//
// The fix mirrors the self-hosted `leading_op_continues` rule rather than
// inventing a new one: the continuation is taken only when the operator sits
// on a STRICTLY MORE DEEPLY INDENTED line, via
// `peek_indented_operator_continuation`. That is what keeps a same-indent
// statement from being swallowed into the previous expression.
//
// Run: cargo test -p simple-parser --test leading_comparison_continuation

fn parses(src: &str) -> bool {
    simple_parser::Parser::new(src).parse().is_ok()
}

fn debug_ast(src: &str) -> String {
    let module = simple_parser::Parser::new(src)
        .parse()
        .unwrap_or_else(|e| panic!("parse failed for:\n{src}\nerror: {e:?}"));
    format!("{module:?}")
}

/// `val x = a\n        <op> b` inside a function body: the canonical
/// deeper-indented leading continuation shape.
fn binding_leading(op: &str) -> String {
    format!("fn f(a: i64, b: i64) -> bool:\n    val x = a\n        {op} b\n    return x\n")
}

/// The same shape in an `if` condition.
fn if_cond_leading(op: &str) -> String {
    format!("fn f(a: i64, b: i64) -> i64:\n    if a\n        {op} b:\n        return 1\n    return 2\n")
}

/// Every operator in the previously-rejected family. `is`/`in` take the same
/// path as `==`/`!=` (`parse_equality`); `??` is postfix.
const COMPARISON_FAMILY: &[&str] = &["==", "!=", "<", ">", "<=", ">="];

#[test]
fn leading_comparison_operator_continuation_parses_in_binding() {
    for op in COMPARISON_FAMILY {
        assert!(
            parses(&binding_leading(op)),
            "leading-operator continuation after `{op}` must parse in a binding:\n{}",
            binding_leading(op)
        );
    }
}

#[test]
fn leading_comparison_operator_continuation_parses_in_if_condition() {
    for op in COMPARISON_FAMILY {
        assert!(
            parses(&if_cond_leading(op)),
            "leading-operator continuation after `{op}` must parse in an if condition:\n{}",
            if_cond_leading(op)
        );
    }
}

#[test]
fn leading_membership_operator_continuation_parses() {
    // `is` and `in` ride `parse_equality` alongside `==`/`!=`.
    let is_src = "fn f(a: i64, b: i64) -> bool:\n    val x = a\n        is b\n    return x\n";
    assert!(parses(is_src), "leading `is` continuation must parse:\n{is_src}");
    let in_src = "fn f(a: i64, b: [i64]) -> bool:\n    val x = a\n        in b\n    return x\n";
    assert!(parses(in_src), "leading `in` continuation must parse:\n{in_src}");
}

#[test]
fn leading_nil_coalesce_continuation_parses() {
    let src = "fn f(a: i64?, b: i64) -> i64:\n    val x = a\n        ?? b\n    return x\n";
    assert!(parses(src), "leading `??` continuation must parse:\n{src}");
}

#[test]
fn leading_comparison_continuation_builds_the_binary_node() {
    // Non-vacuity: parsing successfully is not enough — the operands must
    // actually be joined, not silently split into two statements.
    for (op, node) in [
        ("==", "Eq"),
        ("!=", "NotEq"),
        ("<", "Lt"),
        (">", "Gt"),
        ("<=", "LtEq"),
        (">=", "GtEq"),
    ] {
        let src = binding_leading(op);
        let ast = debug_ast(&src);
        assert!(
            ast.contains(node),
            "leading `{op}` continuation must produce a `{node}` binary node.\nsource:\n{src}\nast:\n{ast}"
        );
    }
}

#[test]
fn same_indent_leading_comparison_is_not_glued() {
    // Mirrors `leading_operator_indent_gate.rs`: the strictly-deeper-indent
    // guard must hold for this family too. A `< b` at the SAME indent as the
    // previous statement has no valid parse, and must NOT be absorbed into the
    // previous expression to manufacture one.
    let src = "fn f(a: i64, b: i64) -> i64:\n    a\n    < b\n";
    assert!(
        !parses(src),
        "same-indent leading `<` must not be glued into the previous statement:\n{src}"
    );
}

#[test]
fn trailing_comparison_continuation_still_parses() {
    // Case 1 (trailing operator, fixed by 023a60a05aa) must be untouched.
    for op in COMPARISON_FAMILY {
        let src = format!("fn f(a: i64, b: i64) -> bool:\n    val x = a {op}\n       b\n    return x\n");
        assert!(parses(&src), "trailing `{op}` continuation must still parse:\n{src}");
    }
}

#[test]
fn deliberate_syntax_error_fixture_still_fails() {
    // The control that separates "my change works" from "the parser stopped
    // rejecting anything". These must ALL stay parse errors.
    let bad = [
        // unterminated call
        "fn f() -> i64:\n    return g(1, 2\n",
        // two leading operators stacked
        "fn f(a: i64, b: i64) -> bool:\n    val x = a\n        == <= b\n    return x\n",
        // binding with no right-hand side at all
        "fn f() -> i64:\n    val x = = 1\n    return x\n",
        // operator immediately followed by end of input
        "fn f(a: i64) -> bool:\n    val x = a ==\n",
        // missing colon on a block header
        "fn f(a: i64) -> i64\n    return a\n",
        // stray closing bracket
        "fn f() -> i64:\n    return 1)\n",
    ];
    for src in bad {
        assert!(
            !parses(src),
            "deliberate syntax error must still be REJECTED — the parser has stopped rejecting things:\n{src}"
        );
    }
}
