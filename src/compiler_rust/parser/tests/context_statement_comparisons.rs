//! BUG-2026-10-12-CONTEXT-COMPARISON: statement dispatch must keep the
//! original implicit-tail comparison, while retaining the context-block DSL.
use simple_parser::ast::{BinOp, Expr, Node};
use simple_parser::{lexer::Lexer, token::TokenKind, Parser};

fn parse(source: &str) -> simple_parser::ast::Module {
    Parser::new(source).parse().unwrap_or_else(|error| panic!("{error}\n{source}"))
}

#[test]
fn original_context_comparison_tail_retains_boolean_ast() {
    let source = "fn custody_matches(context: text, actual: Recorded) -> bool:\n    context != \"\" and context == actual.context_digest\n";
    let module = parse(source);
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    let [Node::Expression(Expr::Binary { op: BinOp::And, left, right })] = function.body.statements.as_slice()
        else { panic!("original tail must be a boolean expression, not a context block") };
    assert!(matches!(&**left, Expr::Binary { op: BinOp::NotEq, left, .. }
        if **left == Expr::Identifier("context".into())));
    assert!(matches!(&**right, Expr::Binary { op: BinOp::Eq, left, .. }
        if **left == Expr::Identifier("context".into())));
}

#[test]
fn context_comparisons_parse_at_statement_and_function_tail_boundaries() {
    for (operator, expected) in [("==", BinOp::Eq), ("!=", BinOp::NotEq),
        ("<", BinOp::Lt), (">", BinOp::Gt), ("<=", BinOp::LtEq), (">=", BinOp::GtEq)] {
        let module = parse(&format!("context {operator} 7\n"));
        assert!(matches!(&module.items[0], Node::Expression(Expr::Binary { op, left, .. })
            if *op == expected && **left == Expr::Identifier("context".into())));
        let module = parse(&format!("fn comparison(context: i64) -> bool:\n    context {operator} 7\n"));
        let Node::Function(function) = &module.items[0] else { panic!("expected function") };
        assert!(matches!(&function.body.statements[0], Node::Expression(Expr::Binary { op, left, .. })
            if *op == expected && **left == Expr::Identifier("context".into())));
        let module = parse(&format!("context active:\n    context {operator} 7\n"));
        let Node::Context(statement) = &module.items[0] else { panic!("expected outer context DSL") };
        assert!(matches!(&statement.body.statements[0], Node::Expression(Expr::Binary { op, left, .. })
            if *op == expected && **left == Expr::Identifier("context".into())));
    }
}

#[test]
fn context_dsl_keeps_its_receiver_body_and_required_colon() {
    let mut lexer = Lexer::new("context active:");
    assert_eq!(lexer.next_token().kind, TokenKind::Context);
    let module = parse("context active:\n    pass\n");
    let Node::Context(statement) = &module.items[0] else { panic!("expected context DSL node") };
    assert_eq!(statement.context, Expr::Identifier("active".into()));
    assert!(matches!(&statement.body.statements[0], Node::Pass(_)));
    assert!(Parser::new("context active\n    pass\n").parse().is_err());
}

#[test]
fn context_identifier_assignment_call_and_bare_tail_are_unchanged() {
    let module = parse("context = 7\ncontext(7)\n");
    assert!(matches!(&module.items[0], Node::Assignment(_)));
    assert!(matches!(&module.items[1], Node::Expression(Expr::Call { .. })));
    let module = parse("fn identity(context: i64) -> i64:\n    context\n");
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    assert!(matches!(&function.body.statements[0], Node::Expression(Expr::Identifier(name)) if name == "context"));
}
