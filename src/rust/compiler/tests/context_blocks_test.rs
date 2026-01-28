// Context blocks integration tests (#1305)
// Tests DSL support with implicit receiver pattern

use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let mut parser = Parser::new(source);
    let module = parser.parse()?;
    Ok(evaluate_module(&module.items)?)
}

#[test]
fn test_context_basic_method_dispatch() {
    let source = r#"
class Builder:
    count: int

    fn __init__(self):
        self.count = 0

    me increment():
        self.count = self.count + 1
        return self

    fn get_count(self):
        return self.count

let builder = Builder()
context builder:
    increment()
    increment()
    increment()

main = builder.get_count()
"#;

    let result = parse_and_eval(source);
    assert_eq!(result.unwrap(), 3, "Context should have called increment 3 times");
}

#[test]
fn test_context_with_parameters() {
    let source = r#"
class ConfigDSL:
    port: int

    fn __init__(self):
        self.port = 0

    me set_port(p):
        self.port = p
        return self

    fn get_port(self):
        return self.port

let cfg = ConfigDSL()
context cfg:
    set_port(8080)

main = cfg.get_port()
"#;

    let result = parse_and_eval(source);
    assert_eq!(result.unwrap(), 8080, "Context should set port to 8080");
}

#[test]
fn test_context_fluent_chaining() {
    let source = r#"
class Calculator:
    value: int

    fn __init__(self):
        self.value = 0

    me add(n):
        self.value = self.value + n
        return self

    me multiply(n):
        self.value = self.value * n
        return self

    fn get(self):
        return self.value

let calc = Calculator()
context calc:
    add(5)
    multiply(2)

main = calc.get()
"#;

    let result = parse_and_eval(source);
    // (0 + 5) * 2 = 10
    assert_eq!(result.unwrap(), 10, "Context should chain operations");
}

#[test]
fn test_context_scope_isolation() {
    let source = r#"
class Counter:
    value: int

    fn __init__(self):
        self.value = 0

    me set(v):
        self.value = v
        return self

    fn get(self):
        return self.value

let obj1 = Counter()
let obj2 = Counter()

context obj1:
    set(10)

context obj2:
    set(20)

main = obj1.get() + obj2.get()
"#;

    let result = parse_and_eval(source);
    // 10 + 20 = 30
    assert_eq!(result.unwrap(), 30, "Context should isolate scopes");
}
