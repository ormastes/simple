//! `return` with its value only on the next (indented) line: bare `return`
//! ends at the newline (same as the self-hosted parser), so the indented line
//! is an orphan block. The seed must say so instead of "expected expression".

use simple_parser::Parser;

#[test]
fn return_value_on_next_line_reports_same_line_requirement() {
    let source = "fn f(a: i64) -> i64:\n    return\n        a + 1\n";
    let err = Parser::new(source).parse().expect_err("must be rejected");
    let msg = format!("{}", err);
    assert!(
        msg.contains("`return` value must be on the same line"),
        "unexpected diagnostic: {}",
        msg
    );
}

#[test]
fn bare_return_and_same_line_return_still_parse() {
    let ok = "fn f(a: i64) -> i64:\n    if a > 0:\n        return\n    return a +\n        1\n";
    assert!(Parser::new(ok).parse().is_ok());
    let ok2 = "fn g():\n    return\n";
    assert!(Parser::new(ok2).parse().is_ok());
}
