// Quick test to check import parsing
use simple_parser::Parser;

fn main() {
    let source = r#"
use crate.test.helpers

fn main() -> i64:
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");

    for item in &ast.items {
        if let simple_parser::Node::UseStmt(use_stmt) = item {
            println!("Import path segments: {:?}", use_stmt.path.segments);
            println!("Import target: {:?}", use_stmt.target);
        }
    }
}
