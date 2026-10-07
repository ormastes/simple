//! Named lexical function calls remain AOP execution join points.
use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(source: &str) -> i32 {
    let module = Parser::new(source).parse().expect("parse advice regression");
    interpreter::evaluate_module(&module.items).expect("execute advice regression")
}

#[test]
fn nested_calls_execute_before_and_wildcard_advice() {
    assert_eq!(run(r#"
var count = 0
val probe = \:
    fn counter():
        count = count + 1
    fn calc_add() -> i64:
        1
    fn calc_sub() -> i64:
        2
    on pc{ execution(* calc*(..)) } use counter before priority 10
    val first = calc_add()
    val second = calc_sub()
    if first != 1 or second != 2: return 10
    count
main = probe()
"#), 2);
}

#[test]
fn nested_calls_select_success_and_error_advice() {
    assert_eq!(run(r#"
var successes = 0
var errors = 0
val probe = \:
    fn success():
        successes = successes + 1
    fn error():
        errors = errors + 1
    fn target(fail: bool) -> Result<i64, text>:
        if fail: return Err("boom")
        Ok(7)
    on pc{ execution(* target(..)) } use success after_success priority 10
    on pc{ execution(* target(..)) } use error after_error priority 10
    val good = target(false)
    val bad = target(true)
    if good.is_err() or not bad.is_err(): return 10
    successes * 10 + errors
main = probe()
"#), 11);
}

#[test]
fn lexical_alias_keeps_target_name_and_advice_scope() {
    assert_eq!(run(r#"
var count = 0
val probe = \:
    fn marker():
        count = count + 1
    fn target() -> i64:
        7
    val alias = target
    on pc{ execution(* target(..)) } use marker before priority 10
    if alias() != 7: return 20
    count
main = probe()
"#), 1);
}
