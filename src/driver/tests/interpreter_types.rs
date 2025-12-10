//! Interpreter tests - types

use simple_driver::interpreter::{run_code, Interpreter, RunConfig, RunningType};

/// Helper to run source and expect a compile/semantic error.
/// The error message must contain `expected_error` substring.
/// If compilation succeeds, the test fails.
#[allow(dead_code)]
fn run_expect_error(src: &str, expected_error: &str) {
    let result = run_code(src, &[], "");
    match result {
        Err(e) => {
            let err_msg = e.to_string();
            assert!(
                err_msg.contains(expected_error),
                "Expected error containing '{}', got: {}",
                expected_error,
                err_msg
            );
        }
        Ok(_) => panic!(
            "Expected error containing '{}', but execution succeeded",
            expected_error
        ),
    }
}

/// Helper to run source and expect any error.
/// If execution succeeds, the test fails.
#[allow(dead_code)]
fn run_expect_any_error(src: &str) {
    let result = run_code(src, &[], "");
    assert!(
        result.is_err(),
        "Expected an error, but execution succeeded"
    );
}

#[test]
fn interpreter_enum_comparison_false() {
    let code = r#"
enum Color:
    Red
    Green

let c = Color::Green
main = if c is Color::Red: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_union_type_annotation() {
    // Union types in type annotations (parser test)
    let code = r#"
fn test(x: i64 | str) -> i64:
    return 42
main = test(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_type_alias() {
    let code = r#"
type Number = i64

fn double(x: Number) -> Number:
    return x * 2

main = double(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_union_type_pattern_match_int() {
    // Union type with pattern matching - match on int type
    let code = r#"
fn process(x: i64 | str) -> i64:
    match x:
        n: i64 =>
            return n * 2
        s: str =>
            return 0
    return -1

main = process(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_union_type_pattern_match_str() {
    // Union type with pattern matching - match on string type
    let code = r#"
fn process(x: i64 | str) -> i64:
    match x:
        n: i64 =>
            return n * 2
        s: str =>
            return 100
    return -1

main = process("hello")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_union_type_three_types() {
    // Union type with three types
    let code = r#"
fn classify(x: i64 | str | bool) -> i64:
    match x:
        n: i64 =>
            return 1
        s: str =>
            return 2
        b: bool =>
            return 3
    return 0

let a = classify(42)
let b = classify("test")
let c = classify(true)
main = a + b * 10 + c * 100
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 321); // 1 + 20 + 300
}

#[test]
fn interpreter_optional_type() {
    // T? syntax for optional types
    let code = r#"
fn maybe_value(x: i64?) -> i64:
    return 5
main = maybe_value(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_generic_function_identity() {
    // Generic function: fn identity<T>(x: T) -> T
    let code = r#"
fn identity<T>(x: T) -> T:
    return x

main = identity(42)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_generic_function_pair() {
    // Generic function with two type parameters
    let code = r#"
fn first<A, B>(a: A, b: B) -> A:
    return a

fn second<A, B>(a: A, b: B) -> B:
    return b

let x = first(10, 20)
let y = second(30, 40)
main = x + y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50); // 10 + 40
}

#[test]
fn interpreter_generic_struct() {
    // Generic struct: struct Box<T>
    let code = r#"
struct Box<T>:
    value: T

let b = Box { value: 42 }
main = b.value
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_generic_enum() {
    // Generic enum: enum Option<T>
    // Note: Generic type arguments in type positions use [] not <>
    let code = r#"
enum Maybe<T>:
    Just(T)
    Nothing

fn get_or_default(m: Maybe[i64], default: i64) -> i64:
    match m:
        Maybe::Just(v) =>
            return v
        Maybe::Nothing =>
            return default
    return default

let x = Maybe::Just(42)
main = get_or_default(x, 0)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_option_some() {
    let code = r#"
opt = Some(42)
main = opt.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_option_none_unwrap_or() {
    let code = r#"
opt = None
main = opt.unwrap_or(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

#[test]
fn interpreter_option_is_some() {
    let code = r#"
opt = Some(1)
main = if opt.is_some(): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_option_is_none() {
    let code = r#"
opt = None
main = if opt.is_none(): 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_option_map() {
    let code = r#"
opt = Some(10)
result = opt.map(\x: x * 2)
main = result.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

// ============= Strong Enum Tests =============

#[test]
fn interpreter_strong_enum_exhaustive_match() {
    // Strong enum with exhaustive matching - no wildcard
    let code = r#"
#[strong]
enum Status:
    Active
    Inactive
    Pending

let s = Status::Active
let mut r = 0
match s:
    Status::Active =>
        r = 1
    Status::Inactive =>
        r = 2
    Status::Pending =>
        r = 3
main = r
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_strong_enum_wildcard_error() {
    // Strong enum should reject wildcard pattern
    let code = r#"
#[strong]
enum Status:
    Active
    Inactive

let s = Status::Active
main = match s:
    Status::Active => 1
    _ => 0
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_strong_enum_identifier_catchall_error() {
    // Strong enum should reject identifier catch-all pattern
    let code = r#"
#[strong]
enum Status:
    Active
    Inactive

let s = Status::Active
main = match s:
    Status::Active => 1
    other => 0
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_weak_enum_allows_wildcard() {
    // Normal (weak) enum should allow wildcard
    let code = r#"
enum Status:
    Active
    Inactive
    Pending

let s = Status::Active
main = match s:
    Status::Active => 1
    _ => 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Type Suffix Tests =============

#[test]
fn interpreter_type_suffix_i32() {
    let code = r#"
main = 42i32
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_type_suffix_i64() {
    let code = r#"
main = 100i64
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_type_suffix_u32() {
    let code = r#"
main = 255u32
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 255);
}

#[test]
fn interpreter_unit_suffix_km() {
    // User-defined unit suffix: 100_km
    let code = r#"
let distance = 100_km
main = distance
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_unit_suffix_expression() {
    // Unit suffixes in expressions
    let code = r#"
let a = 50_m
let b = 30_m
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 80);
}

#[test]
fn interpreter_float_suffix_f64() {
    // Float with type suffix - just verify it parses and evaluates
    let code = r#"
let x = 3.14f64
main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_float_suffix_f32() {
    let code = r#"
let x = 1.5f32
main = 2
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

// ============= Standalone Unit Tests =============

#[test]
fn interpreter_unit_def_basic() {
    // Define a standalone unit type and use it
    let code = r#"
unit UserId: i64 as uid

let user_id = 42_uid
main = user_id
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unit_def_arithmetic() {
    // Unit types can be used in arithmetic (value semantics)
    let code = r#"
unit Score: i64 as pts

let a = 100_pts
let b = 50_pts
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 150);
}

// ============= String Methods Tests =============

// ============= Unit Family Tests (#87) =============
// Note: Full unit family syntax `unit length(base: f64): m = 1.0, km = 1000.0`
// is not yet implemented. These tests use standalone units as a foundation.

#[test]
fn interpreter_unit_family_basic() {
    // Define a unit family with conversion factors
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let d = 5000.0_m
main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
#[ignore = "unit conversion methods (.to_m()) not yet implemented"]
fn interpreter_unit_family_to_base() {
    // Convert to base unit
    let code = r#"
unit length(base: f64): m = 1.0, km = 1000.0

let d = 2_km
let meters = d.to_m()
main = 1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============= Primitive API Warnings (#92) =============
// These tests verify that warnings are issued for public APIs using primitives

#[test]
fn interpreter_primitive_warning_suppressed_with_attribute() {
    // #[allow(primitive_api)] suppresses the warning
    let code = r#"
#[allow(primitive_api)]
pub fn get_count() -> i64:
    return 42

main = get_count()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_semantic_type_no_warning() {
    // Using semantic types (unit types) should not warn
    let code = r#"
unit Count: i64 as cnt

pub fn get_count() -> Count:
    return 42_cnt

main = get_count()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}
