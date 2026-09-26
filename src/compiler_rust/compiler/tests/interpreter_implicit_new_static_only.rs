// Regression: a named-argument class literal must still auto-call a
// NON-static (Python-style) `new`, while a STATIC `new` is never reached from a
// named literal (9b6be7f5c98). Before the fix every named shape skipped `new`,
// so `SlnPyCtor(label: "hi")` built the raw field ("hi") instead of running the
// initializer ("hi!"). Surfaced by
// test/01_unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl.

use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> i32 {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval")
}

#[test]
fn named_literal_auto_calls_non_static_python_style_new() {
    let source = r#"
class PyCtor:
    label: text
    fn new(label: text):
        self.label = label + "!"

val c = PyCtor(label: "hi")
main = if c.label == "hi!": 0 else: 1
"#;
    assert_eq!(parse_and_eval(source), 0, "non-static new must run for a named literal");
}

#[test]
fn named_literal_does_not_reach_self_less_factory_new() {
    // Self-less `fn new(...) -> T` is implicitly static (df9f0ef20ca) AND a
    // factory: a field-named literal must build fields, never run it.
    let source = r#"
class Pair:
    a: i64
    b: i64
    fn new(a: i64, b: i64) -> Pair:
        return Pair(a: 77, b: 77)

val p = Pair(a: 1, b: 2)
main = if p.a == 1 and p.b == 2: 0 else: 1
"#;
    assert_eq!(parse_and_eval(source), 0, "a factory new must not consume a named field literal");
}

#[test]
fn named_literal_with_field_names_does_not_reach_static_new() {
    let source = r#"
class Widget:
    id: i64
    size: i64
    static fn new(size: i64) -> Widget:
        return Widget(id: 77, size: size)

val w = Widget(id: 5, size: 8)
main = if w.id == 5 and w.size == 8: 0 else: 1
"#;
    assert_eq!(parse_and_eval(source), 0, "a static new must not consume a named field literal");
}
