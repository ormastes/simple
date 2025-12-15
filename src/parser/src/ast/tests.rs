use super::*;

#[test]
fn test_expr_integer() {
    let expr = Expr::Integer(42);
    assert_eq!(expr, Expr::Integer(42));
}

#[test]
fn test_binary_expr() {
    let expr = Expr::Binary {
        op: BinOp::Add,
        left: Box::new(Expr::Integer(1)),
        right: Box::new(Expr::Integer(2)),
    };
    if let Expr::Binary { op, .. } = expr {
        assert_eq!(op, BinOp::Add);
    } else {
        panic!("Expected Binary expression");
    }
}

#[test]
fn test_function_def() {
    let func = FunctionDef {
        span: Span::new(0, 10, 1, 1),
        name: "add".to_string(),
        generic_params: vec![],
        params: vec![Parameter {
            span: Span::new(4, 5, 1, 5),
            name: "a".to_string(),
            ty: Some(Type::Simple("Int".to_string())),
            default: None,
            mutability: Mutability::Immutable,
        }],
        return_type: Some(Type::Simple("Int".to_string())),
        body: Block::default(),
        visibility: Visibility::Private,
        effect: None,
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
    };
    assert_eq!(func.name, "add");
    assert_eq!(func.params.len(), 1);
}

#[test]
fn test_generic_function_def() {
    let func = FunctionDef {
        span: Span::new(0, 20, 1, 1),
        name: "identity".to_string(),
        generic_params: vec!["T".to_string()],
        params: vec![Parameter {
            span: Span::new(10, 11, 1, 11),
            name: "x".to_string(),
            ty: Some(Type::Simple("T".to_string())),
            default: None,
            mutability: Mutability::Immutable,
        }],
        return_type: Some(Type::Simple("T".to_string())),
        body: Block::default(),
        visibility: Visibility::Private,
        effect: None,
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
    };
    assert_eq!(func.name, "identity");
    assert_eq!(func.generic_params, vec!["T"]);
}

#[test]
fn test_generic_struct_def() {
    let s = StructDef {
        span: Span::new(0, 30, 1, 1),
        name: "Box".to_string(),
        generic_params: vec!["T".to_string()],
        fields: vec![Field {
            span: Span::new(10, 20, 2, 5),
            name: "value".to_string(),
            ty: Type::Simple("T".to_string()),
            default: None,
            mutability: Mutability::Immutable,
            visibility: Visibility::Private,
        }],
        visibility: Visibility::Private,
        attributes: vec![],
        doc_comment: None,
    };
    assert_eq!(s.name, "Box");
    assert_eq!(s.generic_params, vec!["T"]);
}

#[test]
fn test_doc_comment() {
    let doc =
        DocComment::new("This is a function description.\nIt spans multiple lines.".to_string());
    assert_eq!(
        doc.content,
        "This is a function description.\nIt spans multiple lines."
    );
}

#[test]
fn test_doc_comment_trimming() {
    let doc = DocComment::new("  \n  Description with whitespace  \n  ".to_string());
    assert_eq!(doc.content, "Description with whitespace");
}
