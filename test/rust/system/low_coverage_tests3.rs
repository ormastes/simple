//! Low Coverage Type Tests Part 3
//! Tests for parser types, resolution types, and visibility types
#![allow(unused_imports)]

use std::path::PathBuf;

// =============================================================================
// Parser Token Coverage (parser/src/token.rs)
// =============================================================================

use simple_parser::{FStringToken, NumericSuffix, Span, Token, TokenKind};

#[test]
fn test_span_new() {
    let span = Span::new(0, 10, 1, 1);
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 10);
    assert_eq!(span.line, 1);
    assert_eq!(span.column, 1);
}

#[test]
fn test_span_equality() {
    let s1 = Span::new(0, 5, 1, 1);
    let s2 = Span::new(0, 5, 1, 1);
    let s3 = Span::new(5, 10, 2, 1);

    assert_eq!(s1, s2);
    assert_ne!(s1, s3);
}

#[test]
fn test_token_kind_literals() {
    let _ = TokenKind::Integer(42);
    let _ = TokenKind::Float(3.15);
    let _ = TokenKind::String("hello".to_string());
    let _ = TokenKind::Bool(true);
    let _ = TokenKind::Nil;
}

#[test]
fn test_token_kind_typed_literals() {
    let _ = TokenKind::TypedInteger(100, NumericSuffix::I64);
    let _ = TokenKind::TypedFloat(1.5, NumericSuffix::F32);
    let _ = TokenKind::TypedString("127.0.0.1".to_string(), "ip".to_string());
}

#[test]
fn test_token_kind_keywords() {
    let _ = TokenKind::Fn;
    let _ = TokenKind::Let;
    let _ = TokenKind::Mut;
    let _ = TokenKind::If;
    let _ = TokenKind::Else;
    let _ = TokenKind::For;
    let _ = TokenKind::While;
    let _ = TokenKind::Return;
    let _ = TokenKind::Match;
    let _ = TokenKind::Struct;
    let _ = TokenKind::Class;
    let _ = TokenKind::Enum;
    let _ = TokenKind::Trait;
    let _ = TokenKind::Impl;
    let _ = TokenKind::Actor;
    let _ = TokenKind::Pub;
    let _ = TokenKind::Import;
    let _ = TokenKind::Use;
    let _ = TokenKind::Async;
    let _ = TokenKind::Await;
}

#[test]
fn test_token_kind_operators() {
    let _ = TokenKind::Plus;
    let _ = TokenKind::Minus;
    let _ = TokenKind::Star;
    let _ = TokenKind::Slash;
    let _ = TokenKind::Eq; // ==
    let _ = TokenKind::NotEq; // !=
    let _ = TokenKind::Lt;
    let _ = TokenKind::LtEq; // <=
    let _ = TokenKind::Gt;
    let _ = TokenKind::GtEq; // >=
    let _ = TokenKind::And;
    let _ = TokenKind::Or;
    let _ = TokenKind::Not;
    let _ = TokenKind::DoubleStar; // **
    let _ = TokenKind::Parallel; // //
}

#[test]
fn test_token_kind_delimiters() {
    let _ = TokenKind::LParen;
    let _ = TokenKind::RParen;
    let _ = TokenKind::LBracket;
    let _ = TokenKind::RBracket;
    let _ = TokenKind::LBrace;
    let _ = TokenKind::RBrace;
    let _ = TokenKind::Colon;
    let _ = TokenKind::DoubleColon; // ::
    let _ = TokenKind::Comma;
    let _ = TokenKind::Dot;
    let _ = TokenKind::Arrow;
    let _ = TokenKind::FatArrow;
}

#[test]
fn test_token_creation() {
    let token = Token::new(TokenKind::Integer(42), Span::new(0, 2, 1, 1), "42".to_string());
    assert!(matches!(token.kind, TokenKind::Integer(42)));
}

#[test]
fn test_numeric_suffix_variants() {
    let _ = NumericSuffix::I8;
    let _ = NumericSuffix::I16;
    let _ = NumericSuffix::I32;
    let _ = NumericSuffix::I64;
    let _ = NumericSuffix::U8;
    let _ = NumericSuffix::U16;
    let _ = NumericSuffix::U32;
    let _ = NumericSuffix::U64;
    let _ = NumericSuffix::F32;
    let _ = NumericSuffix::F64;
    let _ = NumericSuffix::Unit("km".to_string());
}

#[test]
fn test_fstring_token_variants() {
    let _ = FStringToken::Literal("hello ".to_string());
    let _ = FStringToken::Expr("x + 1".to_string());
}

#[test]
fn test_fstring_token_in_tokenKind() {
    let parts = vec![
        FStringToken::Literal("Hello ".to_string()),
        FStringToken::Expr("name".to_string()),
        FStringToken::Literal("!".to_string()),
    ];
    let _ = TokenKind::FString(parts);
}

#[test]
fn test_token_kind_symbol() {
    let _ = TokenKind::Symbol("my_symbol".to_string());
}

#[test]
fn test_token_kind_raw_string() {
    let _ = TokenKind::RawString("raw content".to_string());
    let _ = TokenKind::TypedRawString("value".to_string(), "suffix".to_string());
}

// =============================================================================
// Resolution Coverage (dependency_tracker/src/resolution.rs - 0%)
// =============================================================================

use simple_dependency_tracker::{
    resolve, to_dir_path, to_file_path, well_formed, FileKind, FileSystem, ModPath, ResolutionResult, Segment,
};

#[test]
fn test_segment_new() {
    let seg = Segment::new("foo");
    assert!(seg.is_some());
    assert_eq!(seg.unwrap().name(), "foo");
}

#[test]
fn test_segment_empty_name() {
    let seg = Segment::new("");
    assert!(seg.is_none());
}

#[test]
fn test_mod_path_new() {
    let seg1 = Segment::new("crate").unwrap();
    let seg2 = Segment::new("foo").unwrap();
    let path = ModPath::new(vec![seg1, seg2]);
    assert!(path.is_some());
    assert_eq!(path.unwrap().segments().len(), 2);
}

#[test]
fn test_mod_path_empty() {
    let path = ModPath::new(vec![]);
    assert!(path.is_none());
}

#[test]
fn test_mod_path_parse() {
    let path = ModPath::parse("crate.foo.bar");
    assert!(path.is_some());
    let path = path.unwrap();
    assert_eq!(path.segments().len(), 3);
}

#[test]
fn test_mod_path_is_absolute() {
    let path = ModPath::parse("crate.foo").unwrap();
    assert!(path.is_absolute());

    let path = ModPath::parse("foo.bar").unwrap();
    assert!(!path.is_absolute());
}

#[test]
fn test_mod_path_without_crate_prefix() {
    let path = ModPath::parse("crate.foo.bar").unwrap();
    let without = path.without_crate_prefix();
    assert!(without.is_some());
    assert_eq!(without.unwrap().segments().len(), 2);
}

#[test]
fn test_file_kind_variants() {
    let _ = FileKind::File;
    let _ = FileKind::Directory;
}

#[test]
fn test_resolution_result_unique() {
    let result = ResolutionResult::Unique {
        kind: FileKind::File,
        path: PathBuf::from("foo.spl"),
    };
    assert!(matches!(result, ResolutionResult::Unique { .. }));
}

#[test]
fn test_resolution_result_ambiguous() {
    let result = ResolutionResult::Ambiguous {
        file_path: PathBuf::from("foo.spl"),
        dir_path: PathBuf::from("foo/__init__.spl"),
    };
    assert!(matches!(result, ResolutionResult::Ambiguous { .. }));
}

#[test]
fn test_resolution_result_not_found() {
    let result = ResolutionResult::NotFound;
    assert!(matches!(result, ResolutionResult::NotFound));
}

#[test]
fn test_file_system_new() {
    let fs = FileSystem::new();
    let _ = fs;
}

#[test]
fn test_file_system_from_paths() {
    let fs = FileSystem::from_paths(vec!["foo.spl", "bar/__init__.spl"]);
    assert!(fs.exists(std::path::Path::new("foo.spl")));
    assert!(fs.exists(std::path::Path::new("bar/__init__.spl")));
}

#[test]
fn test_file_system_add_file() {
    let mut fs = FileSystem::new();
    fs.add_file("test.spl");
    assert!(fs.exists(std::path::Path::new("test.spl")));
}

#[test]
fn test_to_file_path() {
    let root = std::path::Path::new("/project/src");
    let mp = ModPath::parse("foo.bar").unwrap();
    let path = to_file_path(root, &mp);
    // Should be /project/src/foo/bar.spl
    assert!(path.to_string_lossy().contains("bar.spl"));
}

#[test]
fn test_to_dir_path() {
    let root = std::path::Path::new("/project/src");
    let mp = ModPath::parse("foo.bar").unwrap();
    let path = to_dir_path(root, &mp);
    // Should be /project/src/foo/bar/__init__.spl
    assert!(path.to_string_lossy().contains("__init__.spl"));
}

#[test]
fn test_resolve_not_found() {
    let fs = FileSystem::new();
    let root = std::path::Path::new("/project/src");
    let mp = ModPath::parse("foo.bar").unwrap();
    let result = resolve(&fs, root, &mp);
    assert!(matches!(result, ResolutionResult::NotFound));
}

#[test]
fn test_resolve_found_file() {
    let mut fs = FileSystem::new();
    fs.add_file("/project/src/foo/bar.spl");
    let root = std::path::Path::new("/project/src");
    let mp = ModPath::parse("foo.bar").unwrap();
    let result = resolve(&fs, root, &mp);
    assert!(matches!(
        result,
        ResolutionResult::Unique {
            kind: FileKind::File,
            ..
        }
    ));
}

#[test]
fn test_resolve_found_directory() {
    let mut fs = FileSystem::new();
    fs.add_file("/project/src/foo/bar/__init__.spl");
    let root = std::path::Path::new("/project/src");
    let mp = ModPath::parse("foo.bar").unwrap();
    let result = resolve(&fs, root, &mp);
    assert!(matches!(
        result,
        ResolutionResult::Unique {
            kind: FileKind::Directory,
            ..
        }
    ));
}

#[test]
fn test_resolve_ambiguous() {
    let mut fs = FileSystem::new();
    fs.add_file("/project/src/foo/bar.spl");
    fs.add_file("/project/src/foo/bar/__init__.spl");
    let root = std::path::Path::new("/project/src");
    let mp = ModPath::parse("foo.bar").unwrap();
    let result = resolve(&fs, root, &mp);
    assert!(matches!(result, ResolutionResult::Ambiguous { .. }));
}

#[test]
fn test_well_formed_empty() {
    let fs = FileSystem::new();
    let root = std::path::Path::new("/project/src");
    assert!(well_formed(&fs, root));
}

// =============================================================================
// Visibility Coverage (dependency_tracker/src/visibility.rs - 3.70%)
// =============================================================================

use simple_dependency_tracker::{
    ancestor_visibility, effective_visibility, visibility_meet, DirManifest, EffectiveVisibility, ModDecl,
    ModuleContents, Symbol, SymbolId, Visibility,
};

#[test]
fn test_symbol_id_new() {
    let id = SymbolId::new("my_func");
    assert_eq!(id.name, "my_func");
}

#[test]
fn test_symbol_new() {
    let sym = Symbol::new("my_func", Visibility::Public);
    assert_eq!(sym.id.name, "my_func");
    assert!(sym.visibility.is_public());
}

#[test]
fn test_symbol_public() {
    let sym = Symbol::public("pub_func");
    assert!(sym.visibility.is_public());
}

#[test]
fn test_symbol_private() {
    let sym = Symbol::private("priv_func");
    assert!(sym.visibility.is_private());
}

#[test]
fn test_mod_decl_new() {
    let decl = ModDecl::new("my_mod", true);
    assert_eq!(decl.name, "my_mod");
    assert!(decl.is_pub);
}

#[test]
fn test_mod_decl_public() {
    let decl = ModDecl::public("pub_mod");
    assert!(decl.is_pub);
}

#[test]
fn test_mod_decl_private() {
    let decl = ModDecl::private("priv_mod");
    assert!(!decl.is_pub);
}

#[test]
fn test_dir_manifest_new() {
    let manifest = DirManifest::new("my_dir");
    assert_eq!(manifest.name, "my_dir");
}

#[test]
fn test_dir_manifest_add_child() {
    let mut manifest = DirManifest::new("my_dir");
    manifest.add_child(ModDecl::public("child_mod"));
    assert!(manifest.is_child_public("child_mod"));
}

#[test]
fn test_dir_manifest_is_child_public() {
    let mut manifest = DirManifest::new("dir");
    manifest.add_child(ModDecl::public("pub_child"));
    manifest.add_child(ModDecl::private("priv_child"));

    assert!(manifest.is_child_public("pub_child"));
    assert!(!manifest.is_child_public("priv_child"));
    assert!(!manifest.is_child_public("nonexistent"));
}

#[test]
fn test_dir_manifest_add_export() {
    let mut manifest = DirManifest::new("dir");
    manifest.add_export(SymbolId::new("exported_fn"));
    assert!(manifest.is_exported(&SymbolId::new("exported_fn")));
}

#[test]
fn test_module_contents_new() {
    let contents = ModuleContents::new();
    assert!(contents.symbols.is_empty());
}

#[test]
fn test_module_contents_add_symbol() {
    let mut contents = ModuleContents::new();
    contents.add_symbol(Symbol::public("my_func"));

    let vis = contents.symbol_visibility(&SymbolId::new("my_func"));
    assert!(vis.is_some());
    assert!(vis.unwrap().is_public());
}

#[test]
fn test_effective_visibility_value() {
    let eff = EffectiveVisibility(Visibility::Public);
    assert_eq!(eff.0, Visibility::Public);
}

#[test]
fn test_effective_visibility_function() {
    let contents = ModuleContents::new();
    let manifest = DirManifest::new("dir");

    // effective_visibility(manifest, module_name, mc, sym)
    let result = effective_visibility(&manifest, "test_mod", &contents, &SymbolId::new("missing"));
    // Symbol not found should return private
    assert!(result.is_private());
}

#[test]
fn test_visibility_meet_public_public() {
    assert_eq!(
        visibility_meet(Visibility::Public, Visibility::Public),
        Visibility::Public
    );
}

#[test]
fn test_visibility_meet_public_private() {
    assert_eq!(
        visibility_meet(Visibility::Public, Visibility::Private),
        Visibility::Private
    );
}

#[test]
fn test_visibility_meet_private_public() {
    assert_eq!(
        visibility_meet(Visibility::Private, Visibility::Public),
        Visibility::Private
    );
}

#[test]
fn test_visibility_meet_private_private() {
    assert_eq!(
        visibility_meet(Visibility::Private, Visibility::Private),
        Visibility::Private
    );
}

#[test]
fn test_ancestor_visibility_empty() {
    assert_eq!(ancestor_visibility(&[]), Visibility::Public);
}

#[test]
fn test_ancestor_visibility_all_public() {
    let path = vec![Visibility::Public, Visibility::Public, Visibility::Public];
    assert_eq!(ancestor_visibility(&path), Visibility::Public);
}

#[test]
fn test_ancestor_visibility_with_private() {
    let path = vec![Visibility::Public, Visibility::Private, Visibility::Public];
    assert_eq!(ancestor_visibility(&path), Visibility::Private);
}

// =============================================================================
// Type Crate Coverage (type/src/lib.rs)
// =============================================================================

use simple_type::{lean_infer, LeanExpr, LeanTy, Substitution, Type, TypeChecker, TypeError, TypeScheme};

#[test]
fn test_type_int() {
    let t = Type::Int;
    assert!(matches!(t, Type::Int));
}

#[test]
fn test_type_float() {
    let t = Type::Float;
    assert!(matches!(t, Type::Float));
}

#[test]
fn test_type_bool() {
    let t = Type::Bool;
    assert!(matches!(t, Type::Bool));
}

#[test]
fn test_type_str() {
    let t = Type::Str;
    assert!(matches!(t, Type::Str));
}

#[test]
fn test_type_nil() {
    let t = Type::Nil;
    assert!(matches!(t, Type::Nil));
}

#[test]
fn test_type_var() {
    let t = Type::Var(0);
    assert!(matches!(t, Type::Var(0)));
}

#[test]
fn test_type_function() {
    let t = Type::Function {
        params: vec![Type::Int],
        ret: Box::new(Type::Bool),
    };
    assert!(matches!(t, Type::Function { .. }));
}

#[test]
fn test_type_scheme_mono() {
    let scheme = TypeScheme::mono(Type::Int);
    assert!(scheme.vars.is_empty());
}

#[test]
fn test_type_scheme_poly() {
    let scheme = TypeScheme::poly(
        vec![0, 1],
        Type::Function {
            params: vec![Type::Var(0)],
            ret: Box::new(Type::Var(1)),
        },
    );
    assert_eq!(scheme.vars.len(), 2);
}

#[test]
fn test_substitution_new() {
    let sub = Substitution::new();
    let _ = sub;
}

#[test]
fn test_substitution_insert_and_get() {
    let mut sub = Substitution::new();
    sub.insert(0, Type::Int);
    assert!(sub.get(0).is_some());
    assert!(sub.get(1).is_none());
}

#[test]
fn test_type_apply_subst() {
    let mut sub = Substitution::new();
    sub.insert(0, Type::Int);

    let ty = Type::Var(0);
    let applied = ty.apply_subst(&sub);
    assert!(matches!(applied, Type::Int));
}

#[test]
fn test_type_contains_var() {
    let ty = Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Int),
    };
    assert!(ty.contains_var(0));
    assert!(!ty.contains_var(1));
}

#[test]
fn test_type_checker_new() {
    let checker = TypeChecker::new();
    let _ = checker;
}

#[test]
fn test_type_error_mismatch() {
    let err = TypeError::Mismatch {
        expected: Type::Int,
        found: Type::Bool,
    };
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn test_type_error_undefined() {
    let err = TypeError::Undefined("x".to_string());
    assert!(matches!(err, TypeError::Undefined(_)));
}

#[test]
fn test_type_error_occurs_check() {
    let err = TypeError::OccursCheck {
        var_id: 0,
        ty: Type::Var(0),
    };
    assert!(matches!(err, TypeError::OccursCheck { .. }));
}

#[test]
fn test_type_error_other() {
    let err = TypeError::Other("some error".to_string());
    assert!(matches!(err, TypeError::Other(_)));
}

// =============================================================================
// Lean Type Inference Coverage (type/src/lib.rs)
// =============================================================================

#[test]
fn test_lean_ty_nat() {
    let t = LeanTy::Nat;
    assert!(matches!(t, LeanTy::Nat));
}

#[test]
fn test_lean_ty_bool() {
    let t = LeanTy::Bool;
    assert!(matches!(t, LeanTy::Bool));
}

#[test]
fn test_lean_ty_str() {
    let t = LeanTy::Str;
    assert!(matches!(t, LeanTy::Str));
}

#[test]
fn test_lean_ty_arrow() {
    let t = LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Bool));
    assert!(matches!(t, LeanTy::Arrow(_, _)));
}

#[test]
fn test_lean_expr_lit_nat() {
    let e = LeanExpr::LitNat(42);
    assert!(matches!(e, LeanExpr::LitNat(42)));
}

#[test]
fn test_lean_expr_lit_bool() {
    let e = LeanExpr::LitBool(true);
    assert!(matches!(e, LeanExpr::LitBool(true)));
}

#[test]
fn test_lean_expr_lit_str() {
    let e = LeanExpr::LitStr("hello".to_string());
    assert!(matches!(e, LeanExpr::LitStr(_)));
}

#[test]
fn test_lean_expr_add() {
    let e = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
    assert!(matches!(e, LeanExpr::Add(_, _)));
}

#[test]
fn test_lean_infer_nat() {
    let result = lean_infer(&LeanExpr::LitNat(42));
    assert_eq!(result, Some(LeanTy::Nat));
}

#[test]
fn test_lean_infer_bool() {
    let result = lean_infer(&LeanExpr::LitBool(true));
    assert_eq!(result, Some(LeanTy::Bool));
}

#[test]
fn test_lean_infer_str() {
    let result = lean_infer(&LeanExpr::LitStr("hello".to_string()));
    assert_eq!(result, Some(LeanTy::Str));
}

#[test]
fn test_lean_infer_add() {
    let e = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
    let result = lean_infer(&e);
    assert_eq!(result, Some(LeanTy::Nat));
}
