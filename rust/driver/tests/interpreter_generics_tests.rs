//! Interpreter Generics and Type System Tests
//!
//! Tests for advanced type system features: const generics, where clauses,
//! impl Trait for Type, nested generic types, tuple return types,
//! multiple trait bounds, and associated types.

use simple_driver::interpreter::run_code;

/// Test 1: Const generic parameters - const N: usize
/// From: lib/std/core/array.spl line 1
#[test]
fn stdlib_const_generic_param() {
    let code = r#"
struct Array[T, const N: usize]:
    data: T

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 2: Where clause on function
/// From: lib/std/core/array.spl line 22
#[test]
fn stdlib_where_clause_on_function() {
    let code = r#"
fn filled(value: i64) -> i64 where i64: Copy:
    return value

main = filled(42)
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 42),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 3: impl Trait for Type syntax
/// From: lib/std/core/array.spl line 50
#[test]
fn stdlib_impl_trait_for_type() {
    let code = r#"
trait Len:
    fn len(self) -> i64

struct MyList:
    size: i64

impl Len for MyList:
    fn len(self) -> i64:
        return self.size

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 4: Generic impl with where clause
/// From: lib/std/core/array.spl line 276
#[test]
fn stdlib_generic_impl_with_where() {
    let code = r#"
trait Clone:
    fn clone(self) -> Self

impl Clone for i64:
    fn clone(self) -> i64:
        return self

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 5: Nested generic types - List<Option<T>>
/// From: various stdlib files
#[test]
fn stdlib_nested_generic_types() {
    let code = r#"
struct Container:
    items: List<Option<i64>>

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 6: Tuple return type
/// From: lib/std/doctest/parser.spl
#[test]
fn stdlib_tuple_return_type() {
    let code = r#"
fn get_pair() -> (i64, str):
    return (42, "hello")

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 7: Multiple trait bounds - T: Clone + Default
/// From: various stdlib files
#[test]
fn stdlib_multiple_trait_bounds() {
    let code = r#"
trait Clone:
    fn clone(self) -> Self

trait Default:
    fn default() -> Self

fn make[T]() -> T where T: Clone + Default:
    return T.default()

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 8: Associated type syntax
/// From: lib/std/core/traits.spl
#[test]
fn stdlib_associated_type() {
    let code = r#"
trait Iterator:
    type Item
    fn next(self) -> Option<Self.Item>

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}
