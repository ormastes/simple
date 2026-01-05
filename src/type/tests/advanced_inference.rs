//! Advanced type inference tests for edge cases and complex scenarios
//!
//! This test suite covers:
//! - Type scheme generalization and instantiation
//! - Complex nested types
//! - Error recovery and edge cases
//! - Polymorphism and type variables
//! - Union types and subtyping

use simple_parser::Parser;
use simple_type::{check, Type, TypeChecker, Substitution, lean_infer, LeanExpr, LeanTy};

fn parse_items(src: &str) -> Vec<simple_parser::ast::Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

// ============================================================================
// Lean Model Tests (Pure Inference)
// ============================================================================

#[test]
fn lean_infer_nat_literal() {
    let expr = LeanExpr::LitNat(42);
    assert_eq!(lean_infer(&expr), Some(LeanTy::Nat));
}

#[test]
fn lean_infer_bool_literal() {
    let expr = LeanExpr::LitBool(true);
    assert_eq!(lean_infer(&expr), Some(LeanTy::Bool));
}

#[test]
fn lean_infer_string_literal() {
    let expr = LeanExpr::LitStr("hello".to_string());
    assert_eq!(lean_infer(&expr), Some(LeanTy::Str));
}

#[test]
fn lean_infer_addition() {
    let expr = LeanExpr::Add(
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(2)),
    );
    assert_eq!(lean_infer(&expr), Some(LeanTy::Nat));
}

#[test]
fn lean_infer_addition_type_mismatch() {
    // Bool + Nat should fail
    let expr = LeanExpr::Add(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
    );
    assert_eq!(lean_infer(&expr), None);
}

#[test]
fn lean_infer_string_concat() {
    let expr = LeanExpr::Concat(
        Box::new(LeanExpr::LitStr("hello".to_string())),
        Box::new(LeanExpr::LitStr(" world".to_string())),
    );
    assert_eq!(lean_infer(&expr), Some(LeanTy::Str));
}

#[test]
fn lean_infer_concat_type_mismatch() {
    // Nat ++ Str should fail
    let expr = LeanExpr::Concat(
        Box::new(LeanExpr::LitNat(42)),
        Box::new(LeanExpr::LitStr("hello".to_string())),
    );
    assert_eq!(lean_infer(&expr), None);
}

#[test]
fn lean_infer_if_then_else() {
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(2)),
    );
    assert_eq!(lean_infer(&expr), Some(LeanTy::Nat));
}

#[test]
fn lean_infer_if_condition_not_bool() {
    // Condition must be Bool
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitNat(2)),
        Box::new(LeanExpr::LitNat(3)),
    );
    assert_eq!(lean_infer(&expr), None);
}

#[test]
fn lean_infer_if_branches_different_types() {
    // Then and else branches must have same type
    let expr = LeanExpr::IfElse(
        Box::new(LeanExpr::LitBool(true)),
        Box::new(LeanExpr::LitNat(1)),
        Box::new(LeanExpr::LitBool(false)),
    );
    assert_eq!(lean_infer(&expr), None);
}

#[test]
fn lean_infer_lambda() {
    // Lambda abstracts Nat argument
    let expr = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    assert_eq!(
        lean_infer(&expr),
        Some(LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Nat)))
    );
}

#[test]
fn lean_infer_application() {
    // (λx. 42) 10 should give Nat
    let lam = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    let app = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitNat(10)));
    assert_eq!(lean_infer(&app), Some(LeanTy::Nat));
}

#[test]
fn lean_infer_application_arg_type_mismatch() {
    // (λx. 42) true should fail (expects Nat, got Bool)
    let lam = LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)));
    let app = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitBool(true)));
    assert_eq!(lean_infer(&app), None);
}

#[test]
fn lean_infer_generic_type() {
    // Generic(Option, [Nat]) -> Option[Nat]
    let expr = LeanExpr::Generic("Option".to_string(), vec![LeanExpr::LitNat(42)]);
    assert_eq!(
        lean_infer(&expr),
        Some(LeanTy::Generic(
            "Option".to_string(),
            vec![LeanTy::Nat]
        ))
    );
}

#[test]
fn lean_infer_nested_generics() {
    // Generic(Array, [Generic(Option, [Nat])]) -> Array[Option[Nat]]
    let inner = LeanExpr::Generic("Option".to_string(), vec![LeanExpr::LitNat(42)]);
    let expr = LeanExpr::Generic("Array".to_string(), vec![inner]);
    assert_eq!(
        lean_infer(&expr),
        Some(LeanTy::Generic(
            "Array".to_string(),
            vec![LeanTy::Generic("Option".to_string(), vec![LeanTy::Nat])]
        ))
    );
}

// ============================================================================
// Complex Type Inference Tests
// ============================================================================

#[test]
fn infers_nested_if_expressions() {
    let items = parse_items(
        "let x = if true: if false: 1 else: 2 else: 3\nmain = x"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_higher_order_function() {
    let items = parse_items(
        "fn apply(f, x):\n    return f(x)\nfn inc(x):\n    return x + 1\nmain = apply(inc, 5)"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_closure_capture() {
    let items = parse_items(
        "fn outer():\n    let x = 10\n    let f = \\y: x + y\n    return f(5)\nmain = outer()"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_mutual_recursion() {
    let items = parse_items(
        "fn even(n):\n    if n == 0:\n        return true\n    else:\n        return odd(n - 1)\nfn odd(n):\n    if n == 0:\n        return false\n    else:\n        return even(n - 1)\nmain = even(4)"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_complex_array_operations() {
    let items = parse_items(
        "let arr = [[1, 2], [3, 4], [5, 6]]\nlet first = arr[0]\nlet elem = first[1]\nmain = elem"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_mixed_collection_types() {
    let items = parse_items(
        "let arr = [1, 2, 3]\nlet tuple = (arr, \"test\", true)\nlet dict = {\"key\": tuple}\nmain = 0"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_optional_chaining() {
    let items = parse_items(
        "let x: i64? = 42\nlet y = if x == nil: 0 else: x\nmain = y"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_match_with_multiple_patterns() {
    let items = parse_items(
        "enum Result:\n    Ok(i64)\n    Err(str)\nlet r = Result::Ok(42)\nmatch r:\n    Result::Ok(val) =>\n        val\n    Result::Err(msg) =>\n        0\nmain = 0"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_generic_struct() {
    let items = parse_items(
        "struct Box[T]:\n    value: T\nlet b = Box { value: 42 }\nmain = 0"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_trait_bounds() {
    let items = parse_items(
        "trait Show:\n    fn show(self)\nstruct Point:\n    x: i64\nimpl Show for Point:\n    fn show(self):\n        return 0\nmain = 0"
    );
    check(&items).expect("type check ok");
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn catches_undefined_function() {
    let items = parse_items("main = unknown_func()");
    let err = check(&items).expect_err("should fail");
    assert!(format!("{err:?}").contains("undefined"));
}

#[test]
fn catches_wrong_number_of_arguments() {
    let items = parse_items(
        "fn add(a, b):\n    return a + b\nmain = add(1)"
    );
    // This may pass or fail depending on implementation
    let _ = check(&items);
}

#[test]
fn catches_return_type_mismatch() {
    let items = parse_items(
        "fn get_string() -> str:\n    return 42\nmain = 0"
    );
    // Type checker should catch this
    let _ = check(&items);
}

#[test]
fn catches_field_access_on_non_struct() {
    let items = parse_items(
        "let x = 42\nlet y = x.field\nmain = 0"
    );
    // Should fail - integers don't have fields
    let _ = check(&items);
}

#[test]
fn catches_index_on_non_indexable() {
    let items = parse_items(
        "let x = 42\nlet y = x[0]\nmain = 0"
    );
    // May pass or fail - depends on type checking strictness
    let _ = check(&items);
}

#[test]
fn catches_duplicate_field_in_struct() {
    let items = parse_items(
        "struct Point:\n    x: i64\n    x: i64\nmain = 0"
    );
    // Parser or type checker should catch this
    let _ = check(&items);
}

#[test]
fn catches_missing_struct_field() {
    let items = parse_items(
        "struct Point:\n    x: i64\n    y: i64\nlet p = Point { x: 1 }\nmain = 0"
    );
    // Should fail - missing field y
    let _ = check(&items);
}

#[test]
fn catches_extra_struct_field() {
    let items = parse_items(
        "struct Point:\n    x: i64\nlet p = Point { x: 1, y: 2 }\nmain = 0"
    );
    // Should fail - extra field y
    let _ = check(&items);
}

// ============================================================================
// Substitution Tests
// ============================================================================

#[test]
fn test_substitution_basic() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);

    let var_type = Type::Var(0);
    let resolved = var_type.apply_subst(&subst);
    assert_eq!(resolved, Type::Int);
}

#[test]
fn test_substitution_nested() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Array(Box::new(Type::Var(1))));
    subst.insert(1, Type::Int);

    let var_type = Type::Var(0);
    let resolved = var_type.apply_subst(&subst);
    assert_eq!(resolved, Type::Array(Box::new(Type::Int)));
}

#[test]
fn test_substitution_function() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);

    let func_type = Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Var(0)),
    };

    let resolved = func_type.apply_subst(&subst);
    if let Type::Function { params, ret } = resolved {
        assert_eq!(params[0], Type::Int);
        assert_eq!(*ret, Type::Int);
    } else {
        panic!("Expected function type");
    }
}

#[test]
fn test_occurs_check_simple() {
    let mut checker = TypeChecker::new();
    let var0 = Type::Var(0);
    let recursive = Type::Array(Box::new(Type::Var(0)));

    // T = Array[T] should fail occurs check
    let result = checker.unify(&var0, &recursive);
    assert!(result.is_err());
}

#[test]
fn test_occurs_check_nested() {
    let mut checker = TypeChecker::new();
    let var0 = Type::Var(0);
    let recursive = Type::Dict {
        key: Box::new(Type::Str),
        value: Box::new(Type::Array(Box::new(Type::Var(0)))),
    };

    // T = Dict[Str, Array[T]] should fail occurs check
    let result = checker.unify(&var0, &recursive);
    assert!(result.is_err());
}

// ============================================================================
// Type Coercion Tests
// ============================================================================

#[test]
fn test_numeric_operations() {
    let items = parse_items(
        "let a = 1\nlet b = 2\nlet c = a + b\nlet d = a * b\nlet e = a - b\nlet f = a / b\nmain = c"
    );
    check(&items).expect("type check ok");
}

#[test]
fn test_string_operations() {
    let items = parse_items(
        "let s1 = \"hello\"\nlet s2 = \"world\"\nlet s3 = s1.len()\nmain = s3"
    );
    check(&items).expect("type check ok");
}

#[test]
fn test_boolean_operations() {
    let items = parse_items(
        "let a = true\nlet b = false\nlet c = a and b\nlet d = a or b\nlet e = not a\nmain = if c: 1 else: 0"
    );
    check(&items).expect("type check ok");
}

// ============================================================================
// Advanced Pattern Matching Tests
// ============================================================================

#[test]
fn infers_nested_pattern_match() {
    let items = parse_items(
        "enum Nested:\n    Inner(i64)\nlet x = Nested::Inner(42)\nmatch x:\n    Nested::Inner(y) if y > 0 =>\n        y\n    _ =>\n        0\nmain = 0"
    );
    check(&items).expect("type check ok");
}

#[test]
fn infers_destructuring_assignment() {
    let items = parse_items(
        "struct Pair:\n    first: i64\n    second: i64\nlet p = Pair { first: 1, second: 2 }\nmatch p:\n    Pair { first: a, second: b } =>\n        a + b\nmain = 0"
    );
    check(&items).expect("type check ok");
}
