//! A trailing `?` belongs to a member name only when a call `(` follows.
//!
//! Regression: `x.value?` parsed as a field literally named "value?" instead
//! of field `value` followed by the postfix `?` operator.

use simple_parser::Parser;

fn debug_of(src: &str) -> String {
    let mut parser = Parser::new(src);
    format!("{:?}", parser.parse().expect("parse ok").items)
}

#[test]
fn field_then_postfix_question_is_not_glued() {
    let dbg = debug_of("val y = x.value?\n");
    assert!(!dbg.contains("\"value?\""), "field name glued with `?`: {dbg}");
    assert!(dbg.contains("\"value\""), "field `value` missing: {dbg}");
}

#[test]
fn field_question_in_condition_is_not_glued() {
    let dbg = debug_of("if self.slot_a?:\n    pass\n");
    assert!(!dbg.contains("\"slot_a?\""), "field name glued with `?`: {dbg}");
    assert!(dbg.contains("\"slot_a\""), "field `slot_a` missing: {dbg}");
}

#[test]
fn question_method_call_keeps_suffix() {
    let dbg = debug_of("val e = xs.is_empty?()\n");
    assert!(dbg.contains("\"is_empty?\""), "method `is_empty?` lost suffix: {dbg}");
}

#[test]
fn question_fn_definition_keeps_suffix() {
    let dbg = debug_of("fn iter_empty?() -> bool:\n    true\n");
    assert!(dbg.contains("\"iter_empty?\""), "fn `iter_empty?` lost suffix: {dbg}");
}
