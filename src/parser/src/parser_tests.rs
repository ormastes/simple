use super::*;
use pretty_assertions::assert_eq;

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
}

// === Expression Tests ===

#[test]
fn test_integer_literal() {
    let module = parse("42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Integer(n)) = &module.items[0] {
        assert_eq!(*n, 42);
    } else {
        panic!("Expected integer expression");
    }
}

#[test]
fn test_binary_expression() {
    let module = parse("1 + 2").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
        assert_eq!(*op, BinOp::Add);
        assert_eq!(**left, Expr::Integer(1));
        assert_eq!(**right, Expr::Integer(2));
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_operator_precedence() {
    let module = parse("1 + 2 * 3").unwrap();
    // Should parse as 1 + (2 * 3)
    if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
        assert_eq!(*op, BinOp::Add);
        assert_eq!(**left, Expr::Integer(1));
        if let Expr::Binary { op: inner_op, .. } = &**right {
            assert_eq!(*inner_op, BinOp::Mul);
        } else {
            panic!("Expected nested binary");
        }
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_function_call() {
    let module = parse("foo(1, 2)").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("foo".to_string()));
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_method_call() {
    let module = parse("obj.method(x)").unwrap();
    if let Node::Expression(Expr::MethodCall {
        receiver,
        method,
        args,
    }) = &module.items[0]
    {
        assert_eq!(**receiver, Expr::Identifier("obj".to_string()));
        assert_eq!(method, "method");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected method call");
    }
}

#[test]
fn test_array_literal() {
    let module = parse("[1, 2, 3]").unwrap();
    if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
        assert_eq!(elements.len(), 3);
    } else {
        panic!("Expected array literal");
    }
}

// === Statement Tests ===

#[test]
fn test_let_statement() {
    let module = parse("let x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Immutable);
        if let Pattern::Identifier(name) = &stmt.pattern {
            assert_eq!(name, "x");
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_let_mut_statement() {
    let module = parse("let mut x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Mutable);
    } else {
        panic!("Expected let statement");
    }
}

// === Function Tests ===

#[test]
fn test_function_definition() {
    let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 2);
        assert!(func.return_type.is_some());
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_simple_function() {
    let source = "fn greet():\n    print(\"hello\")";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "greet");
        assert_eq!(func.params.len(), 0);
    } else {
        panic!("Expected function definition");
    }
}

// === Struct Tests ===

#[test]
fn test_struct_definition() {
    let source = "struct Point:\n    x: f64\n    y: f64";
    let module = parse(source).unwrap();
    if let Node::Struct(s) = &module.items[0] {
        assert_eq!(s.name, "Point");
        assert_eq!(s.fields.len(), 2);
    } else {
        panic!("Expected struct definition");
    }
}

// === Enum Tests ===

#[test]
fn test_enum_definition() {
    let source = "enum Option:\n    Some(i64)\n    None";
    let module = parse(source).unwrap();
    if let Node::Enum(e) = &module.items[0] {
        assert_eq!(e.name, "Option");
        assert_eq!(e.variants.len(), 2);
    } else {
        panic!("Expected enum definition");
    }
}

// === Control Flow Tests ===

#[test]
fn test_if_statement() {
    let source = "if x > 0:\n    print(x)";
    let module = parse(source).unwrap();
    if let Node::If(stmt) = &module.items[0] {
        assert!(stmt.else_block.is_none());
        assert!(stmt.elif_branches.is_empty());
    } else {
        panic!("Expected if statement");
    }
}

#[test]
fn test_for_loop() {
    let source = "for i in range(10):\n    print(i)";
    let module = parse(source).unwrap();
    if let Node::For(stmt) = &module.items[0] {
        if let Pattern::Identifier(name) = &stmt.pattern {
            assert_eq!(name, "i");
        }
    } else {
        panic!("Expected for statement");
    }
}

#[test]
fn test_while_loop() {
    let source = "while x > 0:\n    x = x - 1";
    let module = parse(source).unwrap();
    assert!(matches!(&module.items[0], Node::While(_)));
}

// === Pattern Tests ===

#[test]
fn test_tuple_pattern() {
    let source = "let (x, y) = point";
    let module = parse(source).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Tuple(patterns) = &stmt.pattern {
            assert_eq!(patterns.len(), 2);
        } else {
            panic!("Expected tuple pattern");
        }
    }
}

// === Module System Tests (Features #104-111) ===

#[test]
fn test_use_single_item() {
    let module = parse("use crate.core.Option").unwrap();
    if let Node::UseStmt(stmt) = &module.items[0] {
        assert_eq!(stmt.path.segments, vec!["crate".to_string(), "core".to_string()]);
        assert!(matches!(&stmt.target, ImportTarget::Single(name) if name == "Option"));
    } else {
        panic!("Expected use statement");
    }
}

#[test]
fn test_use_group_items() {
    let module = parse("use crate.core.{Option, Result}").unwrap();
    if let Node::UseStmt(stmt) = &module.items[0] {
        assert_eq!(stmt.path.segments, vec!["crate".to_string(), "core".to_string()]);
        if let ImportTarget::Group(targets) = &stmt.target {
            assert_eq!(targets.len(), 2);
        } else {
            panic!("Expected group import");
        }
    } else {
        panic!("Expected use statement");
    }
}

#[test]
fn test_use_glob() {
    let module = parse("use crate.core.*").unwrap();
    if let Node::UseStmt(stmt) = &module.items[0] {
        assert_eq!(stmt.path.segments, vec!["crate".to_string(), "core".to_string()]);
        assert!(matches!(&stmt.target, ImportTarget::Glob));
    } else {
        panic!("Expected use statement");
    }
}

#[test]
fn test_use_with_alias() {
    let module = parse("use crate.core.Option as Opt").unwrap();
    if let Node::UseStmt(stmt) = &module.items[0] {
        if let ImportTarget::Aliased { name, alias } = &stmt.target {
            assert_eq!(name, "Option");
            assert_eq!(alias, "Opt");
        } else {
            panic!("Expected aliased import");
        }
    } else {
        panic!("Expected use statement");
    }
}

#[test]
fn test_mod_declaration() {
    let module = parse("mod router").unwrap();
    if let Node::ModDecl(decl) = &module.items[0] {
        assert_eq!(decl.name, "router");
        assert_eq!(decl.visibility, Visibility::Private);
    } else {
        panic!("Expected mod declaration");
    }
}

#[test]
fn test_pub_mod_declaration() {
    let module = parse("pub mod router").unwrap();
    if let Node::ModDecl(decl) = &module.items[0] {
        assert_eq!(decl.name, "router");
        assert_eq!(decl.visibility, Visibility::Public);
    } else {
        panic!("Expected mod declaration");
    }
}

#[test]
fn test_common_use() {
    let module = parse("common use crate.core.base.*").unwrap();
    if let Node::CommonUseStmt(stmt) = &module.items[0] {
        assert_eq!(stmt.path.segments, vec!["crate".to_string(), "core".to_string(), "base".to_string()]);
        assert!(matches!(&stmt.target, ImportTarget::Glob));
    } else {
        panic!("Expected common use statement");
    }
}

#[test]
fn test_export_use() {
    let module = parse("export use router.Router").unwrap();
    if let Node::ExportUseStmt(stmt) = &module.items[0] {
        assert_eq!(stmt.path.segments, vec!["router".to_string()]);
        assert!(matches!(&stmt.target, ImportTarget::Single(name) if name == "Router"));
    } else {
        panic!("Expected export use statement");
    }
}

#[test]
fn test_auto_import() {
    let module = parse("auto import router.route").unwrap();
    if let Node::AutoImportStmt(stmt) = &module.items[0] {
        assert_eq!(stmt.path.segments, vec!["router".to_string()]);
        assert_eq!(stmt.macro_name, "route");
    } else {
        panic!("Expected auto import statement");
    }
}

// === SIMD Type Tests ===

#[test]
fn test_simd_type_f32x4() {
    // In Simple language, let uses typed patterns, so the type is in the pattern
    let module = parse("let v: vec[4, f32] = x").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Typed { pattern, ty } = &stmt.pattern {
            assert!(matches!(pattern.as_ref(), Pattern::Identifier(n) if n == "v"));
            if let Type::Simd { lanes, element } = ty {
                assert_eq!(*lanes, 4);
                assert!(matches!(element.as_ref(), Type::Simple(n) if n == "f32"));
            } else {
                panic!("Expected SIMD type in typed pattern, got {:?}", ty);
            }
        } else {
            panic!("Expected typed pattern, got {:?}", stmt.pattern);
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_simd_type_i32x8() {
    let module = parse("let v: vec[8, i32] = x").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Typed { ty, .. } = &stmt.pattern {
            if let Type::Simd { lanes, element } = ty {
                assert_eq!(*lanes, 8);
                assert!(matches!(element.as_ref(), Type::Simple(n) if n == "i32"));
            } else {
                panic!("Expected SIMD type in typed pattern, got {:?}", ty);
            }
        } else {
            panic!("Expected typed pattern");
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_simd_type_f64x2() {
    let module = parse("let v: vec[2, f64] = x").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Typed { ty, .. } = &stmt.pattern {
            if let Type::Simd { lanes, element } = ty {
                assert_eq!(*lanes, 2);
                assert!(matches!(element.as_ref(), Type::Simple(n) if n == "f64"));
            } else {
                panic!("Expected SIMD type in typed pattern, got {:?}", ty);
            }
        } else {
            panic!("Expected typed pattern");
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_simd_function_param() {
    let source = "fn add_vectors(a: vec[4, f32], b: vec[4, f32]) -> vec[4, f32]:\n    return a";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.params.len(), 2);

        // Check first param
        if let Some(Type::Simd { lanes, element }) = &func.params[0].ty {
            assert_eq!(*lanes, 4);
            assert!(matches!(element.as_ref(), Type::Simple(n) if n == "f32"));
        } else {
            panic!("Expected SIMD type for first param");
        }

        // Check return type
        if let Some(Type::Simd { lanes, element }) = &func.return_type {
            assert_eq!(*lanes, 4);
            assert!(matches!(element.as_ref(), Type::Simple(n) if n == "f32"));
        } else {
            panic!("Expected SIMD return type");
        }
    } else {
        panic!("Expected function definition");
    }
}

// === Multi-Base Unit Tests ===

#[test]
fn test_single_base_unit() {
    // Standard single-base unit: unit UserId: i64 as uid
    let module = parse("unit UserId: i64 as uid").unwrap();
    assert_eq!(module.items.len(), 1);

    if let Node::Unit(u) = &module.items[0] {
        assert_eq!(u.name, "UserId");
        assert_eq!(u.suffix, "uid");
        assert_eq!(u.base_types.len(), 1);
        assert!(matches!(&u.base_types[0], Type::Simple(n) if n == "i64"));
    } else {
        panic!("Expected unit definition");
    }
}

#[test]
fn test_multi_base_unit() {
    // Multi-base unit: unit IpAddr: str | u32 as ip
    let module = parse("unit IpAddr: str | u32 as ip").unwrap();
    assert_eq!(module.items.len(), 1);

    if let Node::Unit(u) = &module.items[0] {
        assert_eq!(u.name, "IpAddr");
        assert_eq!(u.suffix, "ip");
        assert_eq!(u.base_types.len(), 2);
        assert!(matches!(&u.base_types[0], Type::Simple(n) if n == "str"));
        assert!(matches!(&u.base_types[1], Type::Simple(n) if n == "u32"));
    } else {
        panic!("Expected unit definition");
    }
}

#[test]
fn test_multi_base_unit_three_types() {
    // Two base types: unit MacAddr: str | u64 as mac
    let module = parse("unit MacAddr: str | u64 as mac").unwrap();
    assert_eq!(module.items.len(), 1);

    if let Node::Unit(u) = &module.items[0] {
        assert_eq!(u.name, "MacAddr");
        assert_eq!(u.suffix, "mac");
        assert_eq!(u.base_types.len(), 2);
    } else {
        panic!("Expected unit definition");
    }
}

// === String Unit Suffix Tests ===

#[test]
fn test_typed_string_ip() {
    // String with unit suffix: "127.0.0.1"_ip
    let module = parse(r#"let addr = "127.0.0.1"_ip"#).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Some(Expr::TypedString(value, suffix)) = &stmt.value {
            assert_eq!(value, "127.0.0.1");
            assert_eq!(suffix, "ip");
        } else {
            panic!("Expected TypedString expression, got {:?}", stmt.value);
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_typed_string_file_path() {
    // Raw string with unit suffix: 'C:/Users/data.txt'_file
    let module = parse(r#"let path = 'C:/Users/data.txt'_file"#).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Some(Expr::TypedString(value, suffix)) = &stmt.value {
            assert_eq!(value, "C:/Users/data.txt");
            assert_eq!(suffix, "file");
        } else {
            panic!("Expected TypedString expression, got {:?}", stmt.value);
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_typed_string_url() {
    // URL with unit suffix
    let module = parse(r#"let url = "https://example.com"_http"#).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Some(Expr::TypedString(value, suffix)) = &stmt.value {
            assert_eq!(value, "https://example.com");
            assert_eq!(suffix, "http");
        } else {
            panic!("Expected TypedString expression, got {:?}", stmt.value);
        }
    } else {
        panic!("Expected let statement");
    }
}


// === Doc Comment Tests ===

#[test]
fn test_doc_comment_on_function() {
    let source = r#"/** Adds two numbers together */
fn add(x: Int, y: Int) -> Int:
    return x + y"#;
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "add");
        assert!(func.doc_comment.is_some());
        let doc = func.doc_comment.as_ref().unwrap();
        assert_eq!(doc.content, "Adds two numbers together");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_doc_comment_line_style() {
    let source = r#"## Multiplies two numbers
fn multiply(x: Int, y: Int) -> Int:
    return x * y"#;
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "multiply");
        assert!(func.doc_comment.is_some());
        let doc = func.doc_comment.as_ref().unwrap();
        assert_eq!(doc.content, "Multiplies two numbers");
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_doc_comment_on_struct() {
    let source = r#"/** A point in 2D space */
struct Point:
    x: Int
    y: Int"#;
    let module = parse(source).unwrap();
    if let Node::Struct(s) = &module.items[0] {
        assert_eq!(s.name, "Point");
        assert!(s.doc_comment.is_some());
        let doc = s.doc_comment.as_ref().unwrap();
        assert_eq!(doc.content, "A point in 2D space");
    } else {
        panic!("Expected struct");
    }
}

#[test]
fn test_function_without_doc_comment() {
    let source = "fn no_doc():\n    pass";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.doc_comment.is_none());
    } else {
        panic!("Expected function");
    }
}
