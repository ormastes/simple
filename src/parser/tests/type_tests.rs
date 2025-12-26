use crate::ast::*;
use crate::error::ParseError;
use crate::Parser;
use pretty_assertions::assert_eq;

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
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

// === Array Type Tests ===

#[test]
fn test_dynamic_array_type() {
    // Test [T] array type syntax (dynamic size)
    // Type annotation is in the pattern, not LetStmt.ty
    let src = "let arr: [i32] = x\n";
    let module = parse(src).unwrap();
    if let Node::Let(let_stmt) = &module.items[0] {
        if let Pattern::Typed { ty, .. } = &let_stmt.pattern {
            if let Type::Array { element, size } = ty {
                assert!(matches!(element.as_ref(), Type::Simple(name) if name == "i32"));
                assert!(size.is_none()); // Dynamic array has no size
            } else {
                panic!("Expected array type, got {:?}", ty);
            }
        } else {
            panic!("Expected typed pattern, got {:?}", let_stmt.pattern);
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_fixed_size_array_type() {
    // Test [T; N] array type syntax (fixed size)
    // Type annotation is in the pattern, not LetStmt.ty
    let src = "let arr: [i32; 10] = x\n";
    let module = parse(src).unwrap();
    if let Node::Let(let_stmt) = &module.items[0] {
        if let Pattern::Typed { ty, .. } = &let_stmt.pattern {
            if let Type::Array { element, size } = ty {
                assert!(matches!(element.as_ref(), Type::Simple(name) if name == "i32"));
                assert!(size.is_some()); // Fixed size array
            } else {
                panic!("Expected array type, got {:?}", ty);
            }
        } else {
            panic!("Expected typed pattern, got {:?}", let_stmt.pattern);
        }
    } else {
        panic!("Expected let statement");
    }
}
