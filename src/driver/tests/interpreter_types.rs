//! Interpreter tests - types

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

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

// ============= String Methods Tests =============

