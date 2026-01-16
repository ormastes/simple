use pretty_assertions::assert_eq;
use simple_parser::ast::*;
use simple_parser::error::ParseError;
use simple_parser::Parser;

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
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
        assert_eq!(
            stmt.path.segments,
            vec!["crate".to_string(), "core".to_string(), "base".to_string()]
        );
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

// === SIMD Bounds Block Tests ===

#[test]
fn test_simd_function_no_bounds() {
    let src = r#"@simd
fn add(data: f32[], dst: f32[]):
    dst[0] = data[0]
"#;
    let module = parse(src).unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "add");
        assert!(func.has_simd_decorator());
        assert!(func.bounds_block.is_none());
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_simd_function_with_bounds_block() {
    let src = r#"@simd
fn vector_add(data: f32[], dst: f32[]):
    dst[0] = data[0]

bounds:
    _.dst.over:
        return
    _.dst.under:
        return
"#;
    let module = parse(src).unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "vector_add");
        assert!(func.has_simd_decorator());
        let bounds = func.bounds_block.as_ref().expect("Expected bounds block");
        assert_eq!(bounds.cases.len(), 2);

        // First case: _.dst.over
        if let BoundsPattern::Atom(atom) = &bounds.cases[0].pattern {
            assert_eq!(atom.variable, "dst");
            assert_eq!(atom.kind, BoundsKind::Over);
        } else {
            panic!("Expected atom pattern");
        }

        // Second case: _.dst.under
        if let BoundsPattern::Atom(atom) = &bounds.cases[1].pattern {
            assert_eq!(atom.variable, "dst");
            assert_eq!(atom.kind, BoundsKind::Under);
        } else {
            panic!("Expected atom pattern");
        }
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_bounds_boolean_or() {
    let src = r#"@simd
fn kernel(x: f32[], y: f32[], z: f32[]):
    z[0] = x[0] + y[0]

bounds:
    _.x.under || _.y.under:
        return
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        let bounds = func.bounds_block.as_ref().expect("Expected bounds block");
        assert_eq!(bounds.cases.len(), 1);

        // Pattern: _.x.under || _.y.under
        if let BoundsPattern::Or(left, right) = &bounds.cases[0].pattern {
            if let BoundsPattern::Atom(l) = &**left {
                assert_eq!(l.variable, "x");
                assert_eq!(l.kind, BoundsKind::Under);
            } else {
                panic!("Expected atom on left");
            }
            if let BoundsPattern::Atom(r) = &**right {
                assert_eq!(r.variable, "y");
                assert_eq!(r.kind, BoundsKind::Under);
            } else {
                panic!("Expected atom on right");
            }
        } else {
            panic!("Expected Or pattern");
        }
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_bounds_boolean_and() {
    let src = r#"@simd
fn kernel(src: f32[], dst: f32[]):
    dst[0] = src[0]

bounds:
    _.src.under && _.dst.over:
        return
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        let bounds = func.bounds_block.as_ref().expect("Expected bounds block");
        assert_eq!(bounds.cases.len(), 1);

        // Pattern: _.src.under && _.dst.over
        if let BoundsPattern::And(left, right) = &bounds.cases[0].pattern {
            if let BoundsPattern::Atom(l) = &**left {
                assert_eq!(l.variable, "src");
                assert_eq!(l.kind, BoundsKind::Under);
            } else {
                panic!("Expected atom on left");
            }
            if let BoundsPattern::Atom(r) = &**right {
                assert_eq!(r.variable, "dst");
                assert_eq!(r.kind, BoundsKind::Over);
            } else {
                panic!("Expected atom on right");
            }
        } else {
            panic!("Expected And pattern");
        }
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_bounds_default_catch_all() {
    let src = r#"@simd
fn kernel(data: f32[], dst: f32[]):
    dst[0] = data[0]

bounds:
    _.dst.over:
        return
    _:
        return
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        let bounds = func.bounds_block.as_ref().expect("Expected bounds block");
        assert_eq!(bounds.cases.len(), 2);

        // Second case: _ (default)
        assert_eq!(bounds.cases[1].pattern, BoundsPattern::Default);
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_bounds_with_or_keyword() {
    let src = r#"@simd
fn kernel(src: f32[], dst: f32[]):
    dst[0] = src[0]

bounds:
    _.src.under or _.dst.over:
        return
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        let bounds = func.bounds_block.as_ref().expect("Expected bounds block");
        assert_eq!(bounds.cases.len(), 1);

        // Pattern: _.src.under or _.dst.over (using keyword instead of ||)
        if let BoundsPattern::Or(left, right) = &bounds.cases[0].pattern {
            if let BoundsPattern::Atom(l) = &**left {
                assert_eq!(l.variable, "src");
            } else {
                panic!("Expected atom on left");
            }
            if let BoundsPattern::Atom(r) = &**right {
                assert_eq!(r.variable, "dst");
            } else {
                panic!("Expected atom on right");
            }
        } else {
            panic!("Expected Or pattern");
        }
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_bounds_with_and_keyword() {
    let src = r#"@simd
fn kernel(src: f32[], dst: f32[]):
    dst[0] = src[0]

bounds:
    _.src.under and _.dst.over:
        return
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        let bounds = func.bounds_block.as_ref().expect("Expected bounds block");
        assert_eq!(bounds.cases.len(), 1);

        // Pattern: _.src.under and _.dst.over (using keyword instead of &&)
        if let BoundsPattern::And(left, right) = &bounds.cases[0].pattern {
            if let BoundsPattern::Atom(l) = &**left {
                assert_eq!(l.variable, "src");
            } else {
                panic!("Expected atom on left");
            }
            if let BoundsPattern::Atom(r) = &**right {
                assert_eq!(r.variable, "dst");
            } else {
                panic!("Expected atom on right");
            }
        } else {
            panic!("Expected And pattern");
        }
    } else {
        panic!("Expected function");
    }
}

// === Provenance Tracking Tests (#913) ===

#[test]
fn test_generated_by_decorator_basic() {
    // Test basic @generated_by decorator with tool name
    let src = r#"
@generated_by(tool: "claude")
fn calculate_tax(amount: i64) -> i64:
    return amount * 0.15
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_generated(), "Function should be marked as generated");
        assert_eq!(func.name, "calculate_tax");

        let metadata = func.generated_by_metadata();
        assert!(metadata.is_some(), "Should have provenance metadata");

        let args = metadata.unwrap();
        assert_eq!(args.len(), 1);
        assert_eq!(args[0].name, Some("tool".to_string()));
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_generated_by_decorator_full_metadata() {
    // Test @generated_by with full metadata
    let src = r#"
@generated_by(
    tool: "claude",
    version: "3.5",
    prompt_hash: "sha256:abc123",
    timestamp: "2025-01-15T10:30:00Z"
)
fn process_payment(order: Order) -> Result[Payment]:
    pass
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_generated());

        let metadata = func.generated_by_metadata();
        assert!(metadata.is_some());

        let args = metadata.unwrap();
        assert_eq!(args.len(), 4);

        // Check all metadata fields are present
        let field_names: Vec<_> = args.iter().filter_map(|a| a.name.as_ref()).collect();
        assert!(field_names.contains(&&"tool".to_string()));
        assert!(field_names.contains(&&"version".to_string()));
        assert!(field_names.contains(&&"prompt_hash".to_string()));
        assert!(field_names.contains(&&"timestamp".to_string()));
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_generated_by_with_verification() {
    // Test @generated_by with verification metadata
    let src = r#"
@generated_by(
    tool: "copilot",
    verified: true,
    reviewer: "alice@example.com",
    review_date: "2025-01-16"
)
fn validate_input(data: String) -> bool:
    return true
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_generated());

        let metadata = func.generated_by_metadata();
        assert!(metadata.is_some());

        let args = metadata.unwrap();
        let field_names: Vec<_> = args.iter().filter_map(|a| a.name.as_ref()).collect();
        assert!(field_names.contains(&&"verified".to_string()));
        assert!(field_names.contains(&&"reviewer".to_string()));
        assert!(field_names.contains(&&"review_date".to_string()));
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_generated_by_no_decorator() {
    // Test function without @generated_by decorator
    let src = r#"
fn manual_function(x: i64) -> i64:
    return x + 1
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(!func.is_generated(), "Function should not be marked as generated");
        assert!(
            func.generated_by_metadata().is_none(),
            "Should have no provenance metadata"
        );
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_multiple_decorators_with_generated_by() {
    // Test function with multiple decorators including @generated_by
    let src = r#"
@generated_by(tool: "claude", version: "3.5")
@test
fn test_calculation():
    pass
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.is_generated(), "Should be marked as generated");
        assert!(func.is_test(), "Should also be marked as test");
        assert!(func.generated_by_metadata().is_some());
    } else {
        panic!("Expected function definition");
    }
}
