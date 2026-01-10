//! Type crate integration tests
//! Tests LeanTy, LeanExpr, lean_infer, Type, TypeScheme, and type checking
//! Focus: Public function coverage for simple_type

#![allow(unused_imports, unused_variables)]

use simple_type::{
    check, infer_deterministic, infer_pure, infer_simple, lean_infer, to_simple_expr,
    LeanExpr, LeanTy, SimpleTy, Substitution, Type, TypeChecker, TypeError, TypeScheme,
};

// =============================================================================
// LeanTy Tests
// =============================================================================

#[test]
fn test_lean_ty_nat() {
    let ty = LeanTy::Nat;
    assert_eq!(ty, LeanTy::Nat);
}

#[test]
fn test_lean_ty_bool() {
    let ty = LeanTy::Bool;
    assert_eq!(ty, LeanTy::Bool);
}

#[test]
fn test_lean_ty_str() {
    let ty = LeanTy::Str;
    assert_eq!(ty, LeanTy::Str);
}

#[test]
fn test_lean_ty_arrow() {
    let ty = LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Bool));
    match ty {
        LeanTy::Arrow(arg, ret) => {
            assert_eq!(*arg, LeanTy::Nat);
            assert_eq!(*ret, LeanTy::Bool);
        }
        _ => panic!("Expected arrow type"),
    }
}

#[test]
fn test_lean_ty_generic() {
    let ty = LeanTy::Generic("List".to_string(), vec![LeanTy::Nat]);
    match ty {
        LeanTy::Generic(name, args) => {
            assert_eq!(name, "List");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("Expected generic type"),
    }
}

#[test]
fn test_lean_ty_clone() {
    let ty = LeanTy::Nat;
    let ty2 = ty.clone();
    assert_eq!(ty, ty2);
}

#[test]
fn test_lean_ty_debug() {
    let ty = LeanTy::Nat;
    let debug = format!("{:?}", ty);
    assert!(debug.contains("Nat"));
}

// =============================================================================
// LeanExpr Tests
// =============================================================================

#[test]
fn test_lean_expr_lit_nat() {
    let expr = LeanExpr::LitNat(42);
    match expr {
        LeanExpr::LitNat(n) => assert_eq!(n, 42),
        _ => panic!("Expected LitNat"),
    }
}

#[test]
fn test_lean_expr_lit_bool() {
    let expr = LeanExpr::LitBool(true);
    match expr {
        LeanExpr::LitBool(b) => assert!(b),
        _ => panic!("Expected LitBool"),
    }
}

#[test]
fn test_lean_expr_lit_str() {
    let expr = LeanExpr::LitStr("hello".to_string());
    match expr {
        LeanExpr::LitStr(s) => assert_eq!(s, "hello"),
        _ => panic!("Expected LitStr"),
    }
}

#[test]
fn test_lean_expr_add() {
    let expr = LeanExpr::Add(
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(2)),
    );
    match expr {
        LeanExpr::Add(_, _) => {}
        _ => panic!("Expected Add"),
    }
}

#[test]
fn test_lean_expr_concat() {
    let expr = LeanExpr::Concat(
        Box::new(LeanExpr::LitStr("a".to_string())),
        Box::new(LeanExpr::LitStr("b".to_string())),
    );
    match expr {
        LeanExpr::Concat(_, _) => {}
        _ => panic!("Expected Concat"),
    }
}

#[test]
fn test_lean_expr_if_else() {
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(0)),
    );
    match expr {
        LeanExpr::IfElse(_, _, _) => {}
        _ => panic!("Expected IfElse"),
    }
}

#[test]
fn test_lean_expr_lam() {
    let expr = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    match expr {
        LeanExpr::Lam(_) => {}
        _ => panic!("Expected Lam"),
    }
}

#[test]
fn test_lean_expr_app() {
    let func = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    let expr = LeanExpr::App(Box::new(func), Box::new(LeanExpr::LitNat(10)));
    match expr {
        LeanExpr::App(_, _) => {}
        _ => panic!("Expected App"),
    }
}

#[test]
fn test_lean_expr_generic() {
    let expr = LeanExpr::Generic("Pair".to_string(), vec![
        LeanExpr::LitNat(1),
        LeanExpr::LitStr("hello".to_string()),
    ]);
    match expr {
        LeanExpr::Generic(name, args) => {
            assert_eq!(name, "Pair");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Generic"),
    }
}

// =============================================================================
// lean_infer Tests
// =============================================================================

#[test]
fn test_lean_infer_lit_nat() {
    let expr = LeanExpr::LitNat(42);
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Nat));
}

#[test]
fn test_lean_infer_lit_bool() {
    let expr = LeanExpr::LitBool(true);
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Bool));
}

#[test]
fn test_lean_infer_lit_str() {
    let expr = LeanExpr::LitStr("hello".to_string());
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Str));
}

#[test]
fn test_lean_infer_add_nat() {
    let expr = LeanExpr::Add(
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(2)),
    );
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Nat));
}

#[test]
fn test_lean_infer_add_type_error() {
    // Adding bool + nat should fail
    let expr = LeanExpr::Add(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(2)),
    );
    let ty = lean_infer(&expr);
    assert!(ty.is_none());
}

#[test]
fn test_lean_infer_concat_str() {
    let expr = LeanExpr::Concat(
        Box::new(LeanExpr::LitStr("a".to_string())),
        Box::new(LeanExpr::LitStr("b".to_string())),
    );
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Str));
}

#[test]
fn test_lean_infer_concat_type_error() {
    // Concatenating nat + str should fail
    let expr = LeanExpr::Concat(
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitStr("b".to_string())),
    );
    let ty = lean_infer(&expr);
    assert!(ty.is_none());
}

#[test]
fn test_lean_infer_if_else_nat() {
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(0)),
    );
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Nat));
}

#[test]
fn test_lean_infer_if_else_branch_mismatch() {
    // if true then 1 else "s" - type mismatch
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitStr("s".to_string())),
    );
    let ty = lean_infer(&expr);
    assert!(ty.is_none());
}

#[test]
fn test_lean_infer_if_else_non_bool_cond() {
    // if 1 then 2 else 3 - non-bool condition
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(2)),
        Box::new(LeanExpr::LitNat(3)),
    );
    let ty = lean_infer(&expr);
    assert!(ty.is_none());
}

#[test]
fn test_lean_infer_lam() {
    // \x. 42 : Nat -> Nat
    let expr = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Nat))));
}

#[test]
fn test_lean_infer_app() {
    // (\x. 42) 10
    let func = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    let expr = LeanExpr::App(Box::new(func), Box::new(LeanExpr::LitNat(10)));
    let ty = lean_infer(&expr);
    assert_eq!(ty, Some(LeanTy::Nat));
}

#[test]
fn test_lean_infer_app_type_error() {
    // (\x. 42) true - argument type mismatch (expects Nat)
    let func = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    let expr = LeanExpr::App(Box::new(func), Box::new(LeanExpr::LitBool(true)));
    let ty = lean_infer(&expr);
    assert!(ty.is_none());
}

#[test]
fn test_lean_infer_app_non_function() {
    // 42 10 - applying non-function
    let expr = LeanExpr::App(
        Box::new(LeanExpr::LitNat(42)),
        Box::new(LeanExpr::LitNat(10)),
    );
    let ty = lean_infer(&expr);
    assert!(ty.is_none());
}

#[test]
fn test_lean_infer_generic() {
    let expr = LeanExpr::Generic("List".to_string(), vec![LeanExpr::LitNat(1)]);
    let ty = lean_infer(&expr);
    match ty {
        Some(LeanTy::Generic(name, args)) => {
            assert_eq!(name, "List");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("Expected generic type"),
    }
}

// =============================================================================
// infer_deterministic Tests
// =============================================================================

#[test]
fn test_infer_deterministic_nat() {
    let expr = LeanExpr::LitNat(42);
    assert!(infer_deterministic(&expr));
}

#[test]
fn test_infer_deterministic_complex() {
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(0)),
    );
    assert!(infer_deterministic(&expr));
}

// =============================================================================
// infer_simple / SimpleTy Tests
// =============================================================================

#[test]
fn test_infer_simple_nat() {
    let expr = LeanExpr::LitNat(10);
    let ty = infer_simple(&expr);
    assert_eq!(ty, Some(SimpleTy::Nat));
}

#[test]
fn test_infer_simple_bool() {
    let expr = LeanExpr::LitBool(false);
    let ty = infer_simple(&expr);
    assert_eq!(ty, Some(SimpleTy::Bool));
}

// =============================================================================
// Type Tests
// =============================================================================

#[test]
fn test_type_int() {
    let ty = Type::Int;
    assert_eq!(ty, Type::Int);
}

#[test]
fn test_type_bool() {
    let ty = Type::Bool;
    assert_eq!(ty, Type::Bool);
}

#[test]
fn test_type_str() {
    let ty = Type::Str;
    assert_eq!(ty, Type::Str);
}

#[test]
fn test_type_float() {
    let ty = Type::Float;
    assert_eq!(ty, Type::Float);
}

#[test]
fn test_type_nil() {
    let ty = Type::Nil;
    assert_eq!(ty, Type::Nil);
}

#[test]
fn test_type_var() {
    let ty = Type::Var(0);
    match ty {
        Type::Var(id) => assert_eq!(id, 0),
        _ => panic!("Expected Var"),
    }
}

#[test]
fn test_type_function() {
    let ty = Type::Function {
        params: vec![Type::Int],
        ret: Box::new(Type::Bool),
    };
    match ty {
        Type::Function { params, ret } => {
            assert_eq!(params.len(), 1);
            assert_eq!(*ret, Type::Bool);
        }
        _ => panic!("Expected Function"),
    }
}

#[test]
fn test_type_array() {
    let ty = Type::Array(Box::new(Type::Int));
    match ty {
        Type::Array(elem) => assert_eq!(*elem, Type::Int),
        _ => panic!("Expected Array"),
    }
}

#[test]
fn test_type_union() {
    let ty = Type::Union(vec![Type::Int, Type::Str]);
    match ty {
        Type::Union(types) => assert_eq!(types.len(), 2),
        _ => panic!("Expected Union"),
    }
}

#[test]
fn test_type_generic() {
    let ty = Type::Generic {
        name: "List".to_string(),
        args: vec![Type::Int],
    };
    match ty {
        Type::Generic { name, args } => {
            assert_eq!(name, "List");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("Expected Generic"),
    }
}

#[test]
fn test_type_type_param() {
    let ty = Type::TypeParam("T".to_string());
    match ty {
        Type::TypeParam(name) => assert_eq!(name, "T"),
        _ => panic!("Expected TypeParam"),
    }
}

#[test]
fn test_type_named() {
    let ty = Type::Named("MyStruct".to_string());
    match ty {
        Type::Named(name) => assert_eq!(name, "MyStruct"),
        _ => panic!("Expected Named"),
    }
}

#[test]
fn test_type_tuple() {
    let ty = Type::Tuple(vec![Type::Int, Type::Str]);
    match ty {
        Type::Tuple(types) => assert_eq!(types.len(), 2),
        _ => panic!("Expected Tuple"),
    }
}

#[test]
fn test_type_dict() {
    let ty = Type::Dict {
        key: Box::new(Type::Str),
        value: Box::new(Type::Int),
    };
    match ty {
        Type::Dict { key, value } => {
            assert_eq!(*key, Type::Str);
            assert_eq!(*value, Type::Int);
        }
        _ => panic!("Expected Dict"),
    }
}

#[test]
fn test_type_optional() {
    let ty = Type::Optional(Box::new(Type::Int));
    match ty {
        Type::Optional(inner) => assert_eq!(*inner, Type::Int),
        _ => panic!("Expected Optional"),
    }
}

#[test]
fn test_type_borrow() {
    let ty = Type::Borrow(Box::new(Type::Int));
    match ty {
        Type::Borrow(inner) => assert_eq!(*inner, Type::Int),
        _ => panic!("Expected Borrow"),
    }
}

#[test]
fn test_type_borrow_mut() {
    let ty = Type::BorrowMut(Box::new(Type::Int));
    match ty {
        Type::BorrowMut(inner) => assert_eq!(*inner, Type::Int),
        _ => panic!("Expected BorrowMut"),
    }
}

#[test]
fn test_type_simd() {
    let ty = Type::Simd {
        lanes: 4,
        element: Box::new(Type::Float),
    };
    match ty {
        Type::Simd { lanes, element } => {
            assert_eq!(lanes, 4);
            assert_eq!(*element, Type::Float);
        }
        _ => panic!("Expected Simd"),
    }
}

#[test]
fn test_type_dyn_trait() {
    let ty = Type::DynTrait("MyTrait".to_string());
    match ty {
        Type::DynTrait(name) => assert_eq!(name, "MyTrait"),
        _ => panic!("Expected DynTrait"),
    }
}

#[test]
fn test_type_constructor() {
    let ty = Type::Constructor {
        target: Box::new(Type::Named("MyClass".to_string())),
        args: Some(vec![Type::Int]),
    };
    match ty {
        Type::Constructor { target, args } => {
            assert!(args.is_some());
        }
        _ => panic!("Expected Constructor"),
    }
}

// =============================================================================
// Type::apply_subst Tests
// =============================================================================

#[test]
fn test_type_apply_subst_var() {
    let ty = Type::Var(0);
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);

    let result = ty.apply_subst(&subst);
    assert_eq!(result, Type::Int);
}

#[test]
fn test_type_apply_subst_no_match() {
    let ty = Type::Var(1);
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);

    let result = ty.apply_subst(&subst);
    assert_eq!(result, Type::Var(1));
}

#[test]
fn test_type_apply_subst_function() {
    let ty = Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Var(1)),
    };
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    subst.insert(1, Type::Bool);

    let result = ty.apply_subst(&subst);
    match result {
        Type::Function { params, ret } => {
            assert_eq!(params[0], Type::Int);
            assert_eq!(*ret, Type::Bool);
        }
        _ => panic!("Expected Function"),
    }
}

#[test]
fn test_type_apply_subst_array() {
    let ty = Type::Array(Box::new(Type::Var(0)));
    let mut subst = Substitution::new();
    subst.insert(0, Type::Str);

    let result = ty.apply_subst(&subst);
    match result {
        Type::Array(elem) => assert_eq!(*elem, Type::Str),
        _ => panic!("Expected Array"),
    }
}

// =============================================================================
// Type::contains_var Tests
// =============================================================================

#[test]
fn test_type_contains_var_true() {
    let ty = Type::Var(0);
    assert!(ty.contains_var(0));
}

#[test]
fn test_type_contains_var_false() {
    let ty = Type::Int;
    assert!(!ty.contains_var(0));
}

#[test]
fn test_type_contains_var_function() {
    let ty = Type::Function {
        params: vec![Type::Var(1)],
        ret: Box::new(Type::Int),
    };
    assert!(ty.contains_var(1));
    assert!(!ty.contains_var(0));
}

#[test]
fn test_type_contains_var_nested() {
    let ty = Type::Array(Box::new(Type::Function {
        params: vec![Type::Var(5)],
        ret: Box::new(Type::Bool),
    }));
    assert!(ty.contains_var(5));
    assert!(!ty.contains_var(0));
}

// =============================================================================
// TypeScheme Tests
// =============================================================================

#[test]
fn test_type_scheme_mono() {
    let scheme = TypeScheme::mono(Type::Int);
    assert!(scheme.vars.is_empty());
    assert_eq!(scheme.ty, Type::Int);
}

#[test]
fn test_type_scheme_poly() {
    let scheme = TypeScheme::poly(vec![0, 1], Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Var(1)),
    });
    assert_eq!(scheme.vars.len(), 2);
}

// =============================================================================
// Substitution Tests
// =============================================================================

#[test]
fn test_substitution_new() {
    let subst = Substitution::new();
    assert!(subst.get(0).is_none());
}

#[test]
fn test_substitution_insert_get() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);

    let ty = subst.get(0);
    assert!(ty.is_some());
    assert_eq!(ty.unwrap(), &Type::Int);
}

#[test]
fn test_substitution_compose() {
    let mut subst1 = Substitution::new();
    subst1.insert(0, Type::Var(1));

    let mut subst2 = Substitution::new();
    subst2.insert(1, Type::Int);

    subst1.compose(&subst2);
    // After composition, subst1 should have entries from both
    // Note: compose merges substitutions, doesn't transitively apply them
    let ty0 = subst1.get(0);
    let ty1 = subst1.get(1);
    // var 0 still maps to Var(1), and var 1 maps to Int
    assert_eq!(ty0, Some(&Type::Var(1)));
    assert_eq!(ty1, Some(&Type::Int));
}

#[test]
fn test_substitution_default() {
    let subst = Substitution::default();
    assert!(subst.get(0).is_none());
}

// =============================================================================
// TypeChecker Tests
// =============================================================================

#[test]
fn test_type_checker_new() {
    let checker = TypeChecker::new();
    // Just verify it doesn't panic
    let _ = checker;
}

// =============================================================================
// check function tests
// =============================================================================

#[test]
fn test_check_empty() {
    let result = check(&[]);
    assert!(result.is_ok());
}

// =============================================================================
// to_simple_expr Tests
// =============================================================================

#[test]
fn test_to_simple_expr_integer() {
    use simple_parser::ast::Expr;
    let expr = Expr::Integer(42);
    let simple = to_simple_expr(&expr);
    match simple {
        Some(LeanExpr::LitNat(n)) => assert_eq!(n, 42),
        _ => panic!("Expected LitNat"),
    }
}

#[test]
fn test_to_simple_expr_negative_integer() {
    use simple_parser::ast::Expr;
    let expr = Expr::Integer(-1);
    let simple = to_simple_expr(&expr);
    assert!(simple.is_none()); // Negative numbers not in Lean Nat
}

#[test]
fn test_to_simple_expr_bool() {
    use simple_parser::ast::Expr;
    let expr = Expr::Bool(true);
    let simple = to_simple_expr(&expr);
    match simple {
        Some(LeanExpr::LitBool(b)) => assert!(b),
        _ => panic!("Expected LitBool"),
    }
}

#[test]
fn test_to_simple_expr_string() {
    use simple_parser::ast::Expr;
    let expr = Expr::String("test".to_string());
    let simple = to_simple_expr(&expr);
    match simple {
        Some(LeanExpr::LitStr(s)) => assert_eq!(s, "test"),
        _ => panic!("Expected LitStr"),
    }
}

// =============================================================================
// infer_pure Tests
// =============================================================================

#[test]
fn test_infer_pure_integer() {
    use simple_parser::ast::Expr;
    let expr = Expr::Integer(10);
    let ty = infer_pure(&expr);
    assert_eq!(ty, Some(LeanTy::Nat));
}

#[test]
fn test_infer_pure_bool() {
    use simple_parser::ast::Expr;
    let expr = Expr::Bool(false);
    let ty = infer_pure(&expr);
    assert_eq!(ty, Some(LeanTy::Bool));
}

#[test]
fn test_infer_pure_string() {
    use simple_parser::ast::Expr;
    let expr = Expr::String("hello".to_string());
    let ty = infer_pure(&expr);
    assert_eq!(ty, Some(LeanTy::Str));
}

#[test]
fn test_infer_pure_unsupported() {
    use simple_parser::ast::Expr;
    // Float is not in the Lean model
    let expr = Expr::Float(3.15);
    let ty = infer_pure(&expr);
    assert!(ty.is_none());
}
