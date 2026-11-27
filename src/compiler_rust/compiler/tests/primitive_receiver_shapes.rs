//! Signed named-call receivers use their declared impl without repeating effects.
use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(body: &str) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!(r#"
trait Width:
    fn width() -> i64
impl Width for i32:
    fn width() -> i64: 32
impl Width for i64:
    fn width() -> i64: 64
struct Narrow:
    value: i32
struct Wide:
    value: i64
class Counter:
    calls: i64
struct Rebound:
    value: i64
{body}
"#);
    evaluate_source(&source)
}

fn evaluate_source(source: &str) -> i32 {
    let module = Parser::new(source).parse().expect("receiver fixture parses");
    interpreter::evaluate_module(&module.items).expect("receiver fixture executes")
}

#[test]
fn primitive_call_receiver_preserves_declared_i32_once() {
    assert_eq!(run(r#"
fn getter(counter: Counter) -> i32:
    counter.calls = counter.calls + 1
    7
fn main() -> i32:
    val counter = Counter(calls: 0)
    val selected = getter(counter).width()
    if counter.calls != 1: return 12
    if selected != 32: return 13
    0
"#), 0, "getter must execute once and its i32 return must select i32 impl");
}

#[test]
fn primitive_direct_and_i64_controls() {
    assert_eq!(run(r#"
fn wide_getter() -> i64: 7
fn shadowed() -> i32: 7
fn ambiguous(value: i32) -> i32: 7
fn ambiguous(value: text) -> i64: 7
fn replace_definition():
    struct Rebound:
        value: i32
fn main() -> i32:
    val narrow: i32 = 7
    val wide: i64 = 7
    val holder = Wide(value: 7)
    if narrow.width() != 32: return 21
    if wide.width() != 64: return 22
    if holder.value.width() != 64: return 23
    if wide_getter().width() != 64: return 24
    fn shadowed() -> i64: 7
    if shadowed().width() != 64: return 25
    if ambiguous(7).width() != 64: return 26
    val old = Rebound(value: 7)
    replace_definition()
    if old.value.width() != 64: return 27
    0
"#), 0);
}
