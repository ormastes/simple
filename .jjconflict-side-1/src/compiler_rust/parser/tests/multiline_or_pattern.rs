//! Regression: a `case` or-pattern that wraps onto a continuation line must parse.
//! Bug: doc/08_tracking/bug/multiline_or_pattern_in_case_arm_fails_to_parse_2026-08-17.md

use simple_parser::Parser;

fn parse_result(src: &str) -> Result<(), String> {
    let mut parser = Parser::new(src);
    parser.parse().map(|_| ()).map_err(|e| format!("{:?}", e))
}

#[test]
fn single_line_or_pattern_parses() {
    parse_result("fn f(n: i64) -> i64:\n    match n:\n        case 1 | 2 | 3:\n            return 9\n        case _:\n            return 0\n")
        .expect("single-line or-pattern must parse");
}

#[test]
fn trailing_pipe_continuation_parses() {
    parse_result("fn f(n: i64) -> i64:\n    match n:\n        case 1 | 2 |\n                3:\n            return 9\n        case _:\n            return 0\n")
        .expect("trailing-pipe continuation must parse");
}

#[test]
fn leading_pipe_continuation_parses() {
    parse_result("fn f(n: i64) -> i64:\n    match n:\n        case 1 | 2\n                | 3:\n            return 9\n        case _:\n            return 0\n")
        .expect("leading-pipe continuation must parse");
}
