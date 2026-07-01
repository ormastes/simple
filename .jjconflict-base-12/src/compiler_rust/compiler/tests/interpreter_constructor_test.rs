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
