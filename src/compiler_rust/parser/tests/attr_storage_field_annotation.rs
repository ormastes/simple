use simple_parser::ast::Node;
use simple_parser::Parser;

fn fields_of(source: &str) -> Vec<String> {
    let module = Parser::new(source).parse().expect("attr_storage source parses");
    match &module.items[0] {
        Node::Class(c) => c.fields.iter().map(|f| f.name.clone()).collect(),
        Node::Struct(s) => s.fields.iter().map(|f| f.name.clone()).collect(),
        other => panic!("expected class or struct: {other:?}"),
    }
}

#[test]
fn class_field_pins_are_accepted_and_ignored() {
    let names = fields_of(
        "@node_tree(\"t\")\n@attr_storage(\"column\")\nclass N:\n    @attr_storage(\"sparse_hash\")\n    inferred: text\n    @attr_storage(\"direct\")\n    span: i64\n    op: i64\n",
    );
    assert_eq!(names, vec!["inferred", "span", "op"]);
}

#[test]
fn struct_field_pins_are_accepted_and_ignored() {
    let names = fields_of("struct S:\n    @attr_storage(\"column\")\n    a: i64\n    b: i64\n");
    assert_eq!(names, vec!["a", "b"]);
}

#[test]
fn unknown_field_attribute_is_still_rejected() {
    let err = Parser::new("class N:\n    @bogus_tag(\"x\")\n    a: i64\n").parse();
    assert!(err.is_err());
}
