use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let mut parser = Parser::new(source);
    let module = parser.parse()?;
    Ok(evaluate_module(&module.items)?)
}

#[test]
fn static_new_returns_implicit_object_expression() {
    let source = r#"
class SymbolId:
    id: i64
    name: text

    static fn new(id: i64, name: text) -> SymbolId:
        SymbolId(id: id, name: name)

val sym = SymbolId.new(7, "route")
main = if sym.id == 7: 0 else: 1
"#;

    assert_eq!(parse_and_eval(source).unwrap(), 0);
}

#[test]
fn named_field_literal_does_not_bind_unrelated_new_parameter() {
    let source = r#"
class Thing:
    value: i64

    static fn new(other: i64) -> Thing:
        Thing(value: other + 1)

val thing = Thing(value: 7)
main = if thing.value == 7: 0 else: 1
"#;

    assert_eq!(parse_and_eval(source).unwrap(), 0);
}

#[test]
fn named_field_literal_never_calls_matching_static_new() {
    let source = r#"
class Token:
    value: i64

    static fn new(value: i64) -> Token:
        Token(value: value + 100)

val implicit = Token(value: 7)
val explicit = Token.new(7)
main = if implicit.value == 7 and explicit.value == 107: 0 else: 1
"#;

    assert_eq!(parse_and_eval(source).unwrap(), 0);
}

#[test]
fn mixed_field_literal_never_calls_matching_static_new() {
    let source = r#"
class Pair:
    left: i64
    right: i64

    static fn new(left: i64, right: i64) -> Pair:
        Pair(left: left + 100, right: right + 100)

val pair = Pair(3, right: 4)
main = if pair.left == 3 and pair.right == 4: 0 else: 1
"#;

    assert_eq!(parse_and_eval(source).unwrap(), 0);
}

#[test]
fn named_literal_validates_fields_instead_of_matching_static_new() {
    let source = r#"
class Thing:
    value: i64

    static fn new(other: i64) -> Thing:
        Thing(value: other)

val thing = Thing(other: 7)
main = 0
"#;

    let error = parse_and_eval(source).expect_err("unknown named fields must fail construction");
    assert!(
        error.to_string().contains("has no field named `other`"),
        "unexpected error: {error}"
    );
}

#[test]
fn impl_registers_every_static_method() {
    let source = r#"
struct Config:
    young_size: i64
    old_size: i64

impl Config:
    static fn default() -> Config:
        Config(young_size: 1, old_size: 4)

    static fn with_heap_size(size: i64) -> Config:
        Config(young_size: size / 5, old_size: size * 4 / 5)

val config = Config.with_heap_size(20 * 1024)
val defaults = Config.default()
main = if config.young_size == 4 * 1024 and config.old_size == 16 * 1024 and defaults.old_size == 4: 0 else: 1
"#;

    assert_eq!(parse_and_eval(source).unwrap(), 0);
}

#[test]
fn map_and_dict_new_return_empty_builtin_dicts() {
    let source = r#"
val map_value: Dict<text, i64> = Map.new()
val dict_value: Dict<text, i64> = Dict.new()
main = if map_value.keys().len() == 0 and dict_value.keys().len() == 0: 0 else: 1
"#;

    assert_eq!(parse_and_eval(source).unwrap(), 0);
}
