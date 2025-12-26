//! Interpreter tests - stdlib syntax patterns
//! Testing parsing issues found in stdlib .spl files

use simple_driver::interpreter::run_code;

/// Test 1: Generic type syntax with brackets - Result[T, E]
/// From: lib/std/core/result.spl line 4
/// Error: "expected Colon, found LBracket"
#[test]
fn stdlib_generic_enum_syntax() {
    let code = r#"
enum Result[T, E]:
    Ok(T)
    Err(E)

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 2: Function type syntax - fn(E) -> T
/// From: lib/std/core/result.spl line 37
/// Error: "expected identifier, found Fn"
#[test]
fn stdlib_function_type_syntax() {
    let code = r#"
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    return f(x)

fn double(n: i64) -> i64:
    return n * 2

main = apply(double, 21)
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 42),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 3: Result keyword as type name
/// From: lib/std/doctest/runner.spl
/// Error: "expected identifier, found Result"
#[test]
fn stdlib_result_as_type_name() {
    let code = r#"
fn get_result() -> Result:
    return Ok(42)

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 4: Inline method definition in struct
/// From: lib/std/doctest/parser.spl line 10
/// Error: related to method definition syntax
#[test]
fn stdlib_inline_method_in_struct() {
    let code = r#"
struct Point:
    x: i64
    y: i64

    fn to_string(self) -> str:
        return "Point"

let p = Point { x: 1, y: 2 }
main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 5: Generic type in field - Option[String]
/// From: lib/std/doctest/parser.spl line 18
#[test]
fn stdlib_generic_type_in_field() {
    let code = r#"
struct Container:
    value: Option[str]

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}

/// Test 6: List[String] generic collection type
/// From: lib/std/doctest/parser.spl line 29
#[test]
fn stdlib_list_generic_type() {
    let code = r#"
struct Example:
    items: List[str]

main = 0
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 0),
        Err(e) => panic!("Parse error: {}", e),
    }
}
