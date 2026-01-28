use std::collections::HashMap;

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
        where_clause: vec![],
        params: vec![Parameter {
            span: Span::new(4, 5, 1, 5),
            name: "a".to_string(),
            ty: Some(Type::Simple("Int".to_string())),
            default: None,
            mutability: Mutability::Immutable,
            inject: false,
            variadic: false,
        }],
        return_type: Some(Type::Simple("Int".to_string())),
        body: Block::default(),
        visibility: Visibility::Private,
        effects: vec![],
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
        is_abstract: false,
        bounds_block: None,
        is_sync: false,
        is_me_method: false,
        return_constraint: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: HashMap::new(),
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
        where_clause: vec![],
        params: vec![Parameter {
            span: Span::new(10, 11, 1, 11),
            name: "x".to_string(),
            ty: Some(Type::Simple("T".to_string())),
            default: None,
            mutability: Mutability::Immutable,
            inject: false,
            variadic: false,
        }],
        return_type: Some(Type::Simple("T".to_string())),
        body: Block::default(),
        visibility: Visibility::Private,
        effects: vec![],
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
        is_abstract: false,
        bounds_block: None,
        is_sync: false,
        is_me_method: false,
        return_constraint: None,
        is_generic_template: true,
        specialization_of: None,
        type_bindings: HashMap::new(),
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
        where_clause: vec![],
        fields: vec![Field {
            span: Span::new(10, 20, 2, 5),
            name: "value".to_string(),
            ty: Type::Simple("T".to_string()),
            default: None,
            mutability: Mutability::Immutable,
            visibility: Visibility::Private,
        }],
        methods: vec![],
        visibility: Visibility::Private,
        attributes: vec![],
        doc_comment: None,
        invariant: None,
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

#[test]
fn test_doc_comment_interpolation_parse() {
    let doc = DocComment::new("Before ${examples addition} After".to_string());
    let parts = doc.parse_parts();

    assert_eq!(parts.len(), 3);
    assert_eq!(parts[0], DocPart::Text("Before ".to_string()));
    assert_eq!(parts[1], DocPart::ExamplesRef("addition".to_string()));
    assert_eq!(parts[2], DocPart::Text(" After".to_string()));
}

#[test]
fn test_doc_comment_multiple_interpolations() {
    let doc = DocComment::new("${examples a} middle ${examples b}".to_string());
    let parts = doc.parse_parts();

    assert_eq!(parts.len(), 3);
    assert_eq!(parts[0], DocPart::ExamplesRef("a".to_string()));
    assert_eq!(parts[1], DocPart::Text(" middle ".to_string()));
    assert_eq!(parts[2], DocPart::ExamplesRef("b".to_string()));
}

#[test]
fn test_doc_comment_has_interpolations() {
    let with_interp = DocComment::new("Has ${examples table} here".to_string());
    let without_interp = DocComment::new("No interpolations".to_string());

    assert!(with_interp.has_interpolations());
    assert!(!without_interp.has_interpolations());
}

#[test]
fn test_doc_comment_examples_refs() {
    let doc = DocComment::new("See ${examples addition} and ${examples operation}".to_string());
    let refs = doc.examples_refs();

    assert_eq!(refs, vec!["addition", "operation"]);
}

#[test]
fn test_doc_comment_expand() {
    let doc = DocComment::new("Table:\n${examples data}\nEnd".to_string());

    let expanded = doc.expand(|name| {
        if name == "data" {
            Some("| a | b |\n| 1 | 2 |".to_string())
        } else {
            None
        }
    });

    assert_eq!(expanded, "Table:\n| a | b |\n| 1 | 2 |\nEnd");
}

#[test]
fn test_doc_comment_expand_unknown_ref() {
    let doc = DocComment::new("${examples unknown}".to_string());

    let expanded = doc.expand(|_| None);

    // Unknown refs are kept as-is
    assert_eq!(expanded, "${examples unknown}");
}

#[test]
fn test_doc_comment_no_interpolations() {
    let doc = DocComment::new("Plain text without any interpolations".to_string());
    let parts = doc.parse_parts();

    assert_eq!(parts.len(), 1);
    assert_eq!(parts[0], DocPart::Text("Plain text without any interpolations".to_string()));
}
