//! Tests for lean{} block parsing

use simple_parser::{Parser, Node};

#[test]
fn test_lean_inline_block() {
    let source = r#"
lean{
-- Lean 4 code
theorem test : True := trivial
}

fn main() -> i64:
    0
"#;

    let module = Parser::new(source).parse().expect("Should parse");

    // Find the lean block
    let lean_blocks: Vec<_> = module
        .items
        .iter()
        .filter(|item| matches!(item, Node::LeanBlock(_)))
        .collect();

    assert_eq!(lean_blocks.len(), 1, "Should have one lean block");

    if let Node::LeanBlock(block) = &lean_blocks[0] {
        assert!(block.import_path.is_none(), "Should not have import path");
        assert!(block.code.contains("theorem test"), "Should contain theorem");
    } else {
        panic!("Expected LeanBlock");
    }
}

#[test]
fn test_lean_import_statement() {
    let source = r#"
lean import "proofs/base.lean"

fn main() -> i64:
    0
"#;

    let module = Parser::new(source).parse().expect("Should parse");

    let lean_blocks: Vec<_> = module
        .items
        .iter()
        .filter(|item| matches!(item, Node::LeanBlock(_)))
        .collect();

    assert_eq!(lean_blocks.len(), 1, "Should have one lean block");

    if let Node::LeanBlock(block) = &lean_blocks[0] {
        assert_eq!(block.import_path, Some("proofs/base.lean".to_string()));
        assert!(block.code.is_empty(), "Should have no inline code");
    } else {
        panic!("Expected LeanBlock");
    }
}

#[test]
fn test_lean_as_identifier_in_module_path() {
    // Ensure "lean" can still be used as part of module paths
    let source = r#"
import verification.lean.codegen

fn main() -> i64:
    0
"#;

    let module = Parser::new(source)
        .parse()
        .expect("Should parse - lean is valid in module paths");
    assert!(!module.items.is_empty());
}

#[test]
fn test_multiple_lean_blocks() {
    let source = r#"
lean{
-- First block
theorem first : True := trivial
}

lean import "external.lean"

lean{
-- Second block
theorem second : True := trivial
}

fn main() -> i64:
    0
"#;

    let module = Parser::new(source).parse().expect("Should parse");

    let lean_blocks: Vec<_> = module
        .items
        .iter()
        .filter(|item| matches!(item, Node::LeanBlock(_)))
        .collect();

    assert_eq!(lean_blocks.len(), 3, "Should have three lean blocks");
}
