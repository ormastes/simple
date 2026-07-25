use simple_parser::{Node, Parser};
use simple_parser::ast::ImportTarget;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

#[test]
fn pub_use_single_identifier_becomes_bare_export() {
    let items = parse("pub use DiContainer\n");
    assert_eq!(items.len(), 1);
    match &items[0] {
        Node::ExportUseStmt(stmt) => {
            assert!(stmt.path.segments.is_empty(), "expected bare export path");
            match &stmt.target {
                ImportTarget::Single(name) => assert_eq!(name, "DiContainer"),
                other => panic!("expected single export target, got {:?}", other),
            }
        }
        other => panic!("expected ExportUseStmt, got {:?}", other),
    }
}
