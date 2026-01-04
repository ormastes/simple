use simple_parser::ast::{Node, Type};
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

// Struct definition
#[test]
fn parse_struct_definition() {
    let items = parse("struct Point:\n    x: i64\n    y: i64");
    if let Node::Struct(s) = &items[0] {
        assert_eq!(s.name, "Point");
        assert_eq!(s.fields.len(), 2);
    } else {
        panic!("expected struct");
    }
}

#[test]
fn parse_generic_struct() {
    parse_ok("struct Box<T>:\n    value: T");
}

#[test]
fn parse_struct_where_clause() {
    let items = parse("struct Container<T> where T: Clone:\n    value: T");
    assert_eq!(items.len(), 1);
    if let Node::Struct(s) = &items[0] {
        assert_eq!(s.name, "Container");
        assert_eq!(s.where_clause.len(), 1);
        assert_eq!(s.where_clause[0].type_param, "T");
        assert_eq!(s.where_clause[0].bounds, vec!["Clone"]);
    } else {
        panic!("Expected struct");
    }
}

// Class definition
#[test]
fn parse_class_definition() {
    let items = parse("class Counter:\n    fn count():\n        return 0");
    if let Node::Class(c) = &items[0] {
        assert_eq!(c.name, "Counter");
        assert_eq!(c.methods.len(), 1);
    } else {
        panic!("expected class");
    }
}

// 'new' is a keyword, use 'init' instead
#[test]
fn parse_class_with_methods() {
    parse_ok("class Point:\n    fn init(x, y):\n        self.x = x\n        self.y = y\n    fn distance():\n        return 0");
}

// Enum definitions
#[test]
fn parse_enum_definition() {
    let items = parse("enum Color:\n    Red\n    Green\n    Blue");
    if let Node::Enum(e) = &items[0] {
        assert_eq!(e.name, "Color");
        assert_eq!(e.variants.len(), 3);
    } else {
        panic!("expected enum");
    }
}

#[test]
fn parse_enum_with_payload() {
    let items = parse("enum Option:\n    Some(i64)\n    None");
    if let Node::Enum(e) = &items[0] {
        assert_eq!(e.variants.len(), 2);
    } else {
        panic!("expected enum");
    }
}

// Impl blocks
#[test]
fn parse_impl_block() {
    let items = parse("impl Point:\n    fn origin():\n        return Point { x: 0, y: 0 }");
    if let Node::Impl(i) = &items[0] {
        assert_eq!(i.methods.len(), 1);
    } else {
        panic!("expected impl");
    }
}

#[test]
fn parse_impl_where_clause() {
    parse_ok("impl<T> Clone for Container[T] where T: Clone:\n    fn clone(self) -> Container[T]:\n        return Container(self.value)");
}

#[test]
fn parse_impl_generic_params() {
    let items = parse("impl<T> Clone for Container[T] where T: Clone:\n    fn clone(self) -> Container[T]:\n        return self");
    if let Node::Impl(impl_block) = &items[0] {
        assert_eq!(impl_block.generic_params, vec!["T"]);
        assert_eq!(impl_block.trait_name, Some("Clone".to_string()));
        assert_eq!(impl_block.where_clause.len(), 1);
        assert_eq!(impl_block.where_clause[0].type_param, "T");
    } else {
        panic!("Expected impl block");
    }
}

// Struct init expression
#[test]
fn parse_struct_init_expression() {
    parse_ok("let p = Point { x: 1, y: 2 }");
    parse_ok("let p = Point {}");
}

// Doc comment parsing tests
#[test]
fn parse_struct_with_doc_comment() {
    // Double-quoted strings become FStrings, which the parser handles
    let items = parse("struct Person:\n    \"A person with a name and age.\"\n    name: str\n    age: i64");
    if let Node::Struct(s) = &items[0] {
        assert_eq!(s.name, "Person");
        assert!(s.doc_comment.is_some(), "doc_comment should be present");
        let doc = s.doc_comment.as_ref().unwrap();
        assert_eq!(doc.content, "A person with a name and age.");
        assert_eq!(s.fields.len(), 2);
    } else {
        panic!("expected struct");
    }
}

#[test]
fn parse_class_with_doc_comment() {
    // Double-quoted strings become FStrings, which the parser handles
    let items = parse("class Calculator:\n    \"A simple calculator class.\"\n    fn add(a, b):\n        return a + b");
    if let Node::Class(c) = &items[0] {
        assert_eq!(c.name, "Calculator");
        assert!(c.doc_comment.is_some(), "doc_comment should be present");
        let doc = c.doc_comment.as_ref().unwrap();
        assert_eq!(doc.content, "A simple calculator class.");
        assert_eq!(c.methods.len(), 1);
    } else {
        panic!("expected class");
    }
}

#[test]
fn parse_struct_without_doc_comment() {
    let items = parse("struct Empty:\n    value: i64");
    if let Node::Struct(s) = &items[0] {
        assert_eq!(s.name, "Empty");
        assert!(s.doc_comment.is_none(), "doc_comment should not be present");
        assert_eq!(s.fields.len(), 1);
    } else {
        panic!("expected struct");
    }
}

#[test]
fn parse_class_without_doc_comment() {
    let items = parse("class Basic:\n    fn method():\n        return 0");
    if let Node::Class(c) = &items[0] {
        assert_eq!(c.name, "Basic");
        assert!(c.doc_comment.is_none(), "doc_comment should not be present");
    } else {
        panic!("expected class");
    }
}
