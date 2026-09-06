//! Parenthesis-free matcher-word `expect` form.
//!
//! Regression coverage for the silent no-op where `expect <a> to_equal <b>`
//! parsed as two unrelated statements — `expect(a)` plus an orphan
//! `to_equal(b)` — so no assertion was ever registered on the `simple run`
//! path. See doc/08_tracking/bug/
//! test_runner_multi_path_drops_all_but_first_2026-08-01.md.

use simple_parser::ast::{Expr, Node};
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    parser.parse().expect("parse ok").items
}

/// Returns (matcher_name, matcher_arg_count) for a folded
/// `expect(<subject>).<matcher>(<expected>)` statement.
fn matcher_of(node: &Node) -> Option<(String, usize)> {
    let Node::Expression(Expr::MethodCall {
        receiver, method, args, ..
    }) = node
    else {
        return None;
    };
    let Expr::Call {
        callee,
        args: recv_args,
    } = receiver.as_ref()
    else {
        return None;
    };
    if !matches!(callee.as_ref(), Expr::Identifier(n) if n == "expect") || recv_args.len() != 1 {
        return None;
    }
    Some((method.clone(), args.len()))
}

#[test]
fn matcher_word_form_folds_into_a_single_matcher_call() {
    for (src, matcher) in [
        ("expect 1 to_equal 2\n", "to_equal"),
        ("expect 1 to_be 2\n", "to_be"),
        ("expect actual to_equal expected\n", "to_equal"),
        ("expect obj.value() to_equal 7\n", "to_equal"),
        ("expect \"abc\" to_contain \"b\"\n", "to_contain"),
        ("expect 1 to_be_greater_than 5\n", "to_be_greater_than"),
        ("expect 5 to_be_less_than 1\n", "to_be_less_than"),
        ("expect name to_start_with \"a\"\n", "to_start_with"),
        ("expect name to_end_with \"z\"\n", "to_end_with"),
        ("expect 1 to_not_equal 1\n", "to_not_equal"),
    ] {
        let items = parse(src);
        assert_eq!(items.len(), 1, "{src:?} must be ONE statement, not a split pair");
        let (found, argc) =
            matcher_of(&items[0]).unwrap_or_else(|| panic!("{src:?} did not fold into expect(..).matcher(..)"));
        assert_eq!(found, matcher, "{src:?}");
        assert_eq!(argc, 1, "{src:?} matcher must carry its expected value");
    }
}

#[test]
fn zero_argument_matcher_word_folds_without_an_argument() {
    let items = parse("expect value to_be_nil\n");
    assert_eq!(items.len(), 1);
    assert_eq!(matcher_of(&items[0]), Some(("to_be_nil".to_string(), 0)));
}

#[test]
fn comparison_and_method_forms_are_untouched() {
    // `expect a == b` stays a single bare expect over a Binary argument.
    let items = parse("expect 1 == 2\n");
    assert_eq!(items.len(), 1);
    assert!(matcher_of(&items[0]).is_none());
    match &items[0] {
        Node::Expression(Expr::Call { callee, args }) => {
            assert!(matches!(callee.as_ref(), Expr::Identifier(n) if n == "expect"));
            assert!(matches!(args[0].value, Expr::Binary { .. }));
        }
        other => panic!("unexpected node: {other:?}"),
    }
    // The explicit method form already worked and must keep its shape.
    let items = parse("expect(1).to_equal(2)\n");
    assert_eq!(items.len(), 1);
    assert_eq!(matcher_of(&items[0]), Some(("to_equal".to_string(), 1)));
}

#[test]
fn non_matcher_identifier_after_expect_is_not_folded() {
    // `not_to_equal` is not a known matcher word: leave it alone so it keeps
    // erroring loudly instead of being silently reinterpreted.
    let items = parse("expect 1 not_to_equal 1\n");
    assert!(matcher_of(items.first().unwrap()).is_none());
}
