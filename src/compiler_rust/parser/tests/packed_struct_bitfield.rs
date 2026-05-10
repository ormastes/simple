use simple_parser::ast::{Node, Attribute};
use simple_parser::Parser;

/// Helper: parse source and return the first top-level node.
fn parse_first(src: &str) -> Node {
    let mut parser = Parser::new(src);
    let nodes = parser.parse().expect("parse should succeed");
    nodes.into_iter().next().expect("at least one node")
}

#[test]
fn packed_struct_with_bit_width_fields_parses_successfully() {
    // FR-DRIVER-0003: `@packed struct` with `field: Type:N` annotations must parse.
    let node = parse_first("@packed\nstruct Flags:\n    mode: u16:4\n");
    match node {
        Node::Struct(s) => {
            assert_eq!(s.name, "Flags");
            assert_eq!(s.fields.len(), 1);
            assert_eq!(s.fields[0].name, "mode");
            assert_eq!(s.fields[0].bit_width, Some(4));
            // @packed lands in attributes
            assert!(
                s.attributes.iter().any(|a: &Attribute| a.name == "packed"),
                "expected @packed attribute on struct"
            );
        }
        other => panic!("expected Node::Struct, got {:?}", other),
    }
}

#[test]
fn packed_struct_multi_field_bit_widths_parse_correctly() {
    let src = "@packed\nstruct StatusReg:\n    carry: u32:1\n    zero: u32:1\n    overflow: u32:1\n    reserved: u32:5\n";
    let node = parse_first(src);
    match node {
        Node::Struct(s) => {
            assert_eq!(s.name, "StatusReg");
            assert_eq!(s.fields.len(), 4);
            assert_eq!(s.fields[0].bit_width, Some(1));
            assert_eq!(s.fields[1].bit_width, Some(1));
            assert_eq!(s.fields[2].bit_width, Some(1));
            assert_eq!(s.fields[3].bit_width, Some(5));
        }
        other => panic!("expected Node::Struct, got {:?}", other),
    }
}

#[test]
fn ordinary_struct_fields_have_no_bit_width() {
    let node = parse_first("struct Point:\n    x: i64\n    y: i64\n");
    match node {
        Node::Struct(s) => {
            assert!(s.fields.iter().all(|f| f.bit_width.is_none()));
        }
        other => panic!("expected Node::Struct, got {:?}", other),
    }
}

#[test]
fn reject_post_name_packed_struct_syntax_with_targeted_diagnostic() {
    let mut parser = Parser::new("struct Flags @packed { mode: u16:4 }\n");
    let err = parser
        .parse()
        .expect_err("post-name @packed syntax should be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("post-name @packed struct syntax") || msg.contains("not supported"),
        "expected post-name error, got: {msg}"
    );
}
