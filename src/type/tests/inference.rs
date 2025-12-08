use simple_parser::Parser;
use simple_type::check;

fn parse_items(src: &str) -> Vec<simple_parser::ast::Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

#[test]
fn infers_let_and_function_return() {
    let items = parse_items("let x = 1 + 2\nlet y = x + 3\nmain = y");
    check(&items).expect("type check ok");
}

#[test]
fn catches_undefined_variable() {
    let items = parse_items("main = y + 1");
    let err = check(&items).expect_err("should fail");
    assert!(format!("{err:?}").contains("undefined identifier"));
}
