use simple_parser::ast::*;
use simple_parser::token::TokenKind;
use simple_parser::Parser;

// ============================================================
// 1. match~ (MatchSuspend)
// ============================================================

#[test]
fn test_match_suspend_lexes() {
    let mut lexer = simple_parser::lexer::Lexer::new("match~");
    let tok = lexer.next_token();
    assert_eq!(tok.kind, TokenKind::MatchSuspend);
}

#[test]
fn test_match_suspend_parses() {
    let src = "match~ result:\n    case Ok(v): v\n    case Err(e): 0\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Match(stmt) => {
            assert!(stmt.is_suspend, "match~ should have is_suspend=true");
            assert_eq!(stmt.arms.len(), 2);
        }
        other => panic!("Expected Match node, got {:?}", other),
    }
}

#[test]
fn test_regular_match_not_suspend() {
    let src = "match result:\n    case Ok(v): v\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    match &module.items[0] {
        Node::Match(stmt) => {
            assert!(!stmt.is_suspend, "regular match should have is_suspend=false");
        }
        other => panic!("Expected Match node, got {:?}", other),
    }
}

// ============================================================
// 2. exists as method name
// ============================================================

#[test]
fn test_exists_as_method_name() {
    // Previously this would error; now it should parse as a method call
    let src = "file.exists(path)\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Expression(expr) => match expr {
            Expr::MethodCall {
                receiver: _, method, ..
            } => {
                assert_eq!(method, "exists");
            }
            other => panic!("Expected MethodCall, got {:?}", other),
        },
        other => panic!("Expected Expression node, got {:?}", other),
    }
}

#[test]
fn test_exists_as_no_paren_method() {
    // obj.exists should work without parens too
    let src = "val x = fs.exists\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
}

// ============================================================
// 3. Implicit val/var
// ============================================================

// NOTE: Implicit val/var is experimental/future and currently disabled.
// `name = expr` parses as assignment (not implicit val) because the parser
// cannot distinguish new bindings from reassignment without scope analysis.
// The parse_implicit_val() method exists in var_decl.rs for future use.
#[test]
fn test_implicit_val_disabled() {
    // With implicit val disabled, `name = "Alice"` is a regular assignment
    let src = "name = \"Alice\"\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    assert!(matches!(&module.items[0], Node::Assignment(_)));
}

#[test]
fn test_implicit_var_disabled() {
    // With implicit val disabled, `count_ = 0` is a regular assignment
    let src = "count_ = 0\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    assert!(matches!(&module.items[0], Node::Assignment(_)));
}

#[test]
fn test_implicit_val_does_not_trigger_for_field_assign() {
    // obj.field = value should NOT be implicit val — it should be assignment
    let src = "obj.field = 42\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Assignment(_) => {} // correct: field assignment
        other => panic!("Expected Assignment for field assign, got {:?}", other),
    }
}

#[test]
fn test_implicit_val_does_not_trigger_for_compound_assign() {
    // x += 1 should NOT be implicit val
    let src = "x += 1\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Assignment(stmt) => {
            assert_eq!(stmt.op, AssignOp::AddAssign);
        }
        other => panic!("Expected Assignment for compound assign, got {:?}", other),
    }
}

#[test]
fn test_implicit_val_does_not_trigger_for_private_names() {
    // _private = value should NOT trigger implicit val (private convention)
    let src = "_private = 42\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Assignment(_) => {} // correct: regular assignment
        other => panic!("Expected Assignment for _private, got {:?}", other),
    }
}

#[test]
fn test_implicit_val_does_not_trigger_for_constants() {
    // MY_CONST = 42 should NOT trigger implicit val (constant convention)
    let src = "MY_CONST = 42\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Assignment(_) => {} // correct: regular assignment
        other => panic!("Expected Assignment for constant, got {:?}", other),
    }
}

#[test]
fn test_implicit_val_does_not_trigger_for_type_names() {
    // Point = something should NOT trigger implicit val (TypeName convention)
    let src = "Point = origin\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Assignment(_) => {} // correct: regular assignment
        other => panic!("Expected Assignment for TypeName, got {:?}", other),
    }
}

#[test]
fn test_explicit_val_still_works() {
    let src = "val x = 10\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Let(stmt) => {
            assert_eq!(stmt.mutability, Mutability::Immutable);
        }
        other => panic!("Expected Let node for explicit val, got {:?}", other),
    }
}

#[test]
fn test_explicit_var_still_works() {
    let src = "var y = 20\n";
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap();
    assert_eq!(module.items.len(), 1);
    match &module.items[0] {
        Node::Let(stmt) => {
            assert_eq!(stmt.mutability, Mutability::Mutable);
        }
        other => panic!("Expected Let node for explicit var, got {:?}", other),
    }
}
