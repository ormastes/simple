//! Interpreter Advanced Features Tests
//!
//! Tests for advanced language features: decorators, attributes, Result type,
//! ? operator, match guards, if let/while let, or patterns, range patterns,
//! and numeric literals (hex, binary, octal).

#![allow(unused_imports)]

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_multiple_decorators() {
    // Multiple decorators stacked
    let code = r#"
fn add_ten(f):
    fn wrapper(x):
        return f(x) + 10
    return wrapper

fn double(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@add_ten
@double
fn identity(x):
    return x

main = identity(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    // identity(5) = 5, double -> 10, add_ten -> 20
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_decorator_no_parens() {
    // Simple decorator without parentheses - just verifies the syntax works
    // (This is essentially the same as decorator_basic but confirms no-parens syntax)
    let code = r#"
fn add_five(f):
    fn wrapper(x):
        return f(x) + 5
    return wrapper

@add_five
fn square(x):
    return x * x

main = square(4)
"#;
    let result = run_code(code, &[], "").unwrap();
    // square(4) = 16, then + 5 = 21
    assert_eq!(result.exit_code, 21);
}

// ============= Attributes =============
// Attributes are compile-time metadata that can be attached to items.
// Currently we support: #[inline], #[deprecated], #[allow(...)]

#[test]
fn interpreter_attribute_inline() {
    // #[inline] is a hint for the compiler - doesn't affect runtime behavior
    let code = r#"
#[inline]
fn add(a, b):
    return a + b

main = add(3, 4)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 7);
}

#[test]
fn interpreter_attribute_deprecated() {
    // #[deprecated] marks an item as deprecated - still usable but may warn
    let code = r#"
#[deprecated]
fn old_api(x):
    return x * 2

main = old_api(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_attribute_with_value() {
    // #[deprecated = "message"] - attribute with value
    let code = r#"
#[deprecated = "use new_api instead"]
fn legacy(x):
    return x + 1

main = legacy(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

#[test]
fn interpreter_multiple_attributes() {
    // Multiple attributes on same function
    let code = r#"
#[inline]
#[deprecated]
fn double(x):
    return x * 2

main = double(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_attribute_on_class() {
    // Attributes on class - just verify parsing, execution uses simpler pattern
    let code = r#"
#[deprecated]
class Point:
    x: int
    y: int

# Since class instantiation with __init__ has limitations, just verify parsing
# and return a constant to confirm attributes didn't break anything
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============= Result Type =============
// Result<T, E> for explicit error handling with Ok and Err variants

#[test]
fn interpreter_result_ok_unwrap() {
    // Basic Result with Ok variant - test unwrap
    let code = r#"
res = Ok(42)
main = res.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_result_is_ok() {
    // Check if result is Ok
    let code = r#"
res = Ok(10)
var x = 0
if res.is_ok():
    x = 1
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_result_is_err() {
    // Check if result is Err
    let code = r#"
res = Err("error")
var x = 0
if res.is_err():
    x = 1
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_result_unwrap_or() {
    // Unwrap with default value for Err
    let code = r#"
err_result = Err("oops")
main = err_result.unwrap_or(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

#[test]
fn interpreter_result_from_function() {
    // Function returning Result
    let code = r#"
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

r = safe_divide(20, 4)
main = r.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_result_err_handling() {
    // Function returning Err, handle with unwrap_or
    let code = r#"
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

r = safe_divide(10, 0)
main = r.unwrap_or(-1)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -1);
}

// ============= ? Operator =============
// The ? operator for error propagation (early return on Err)

#[test]
fn interpreter_question_mark_operator() {
    // ? operator propagates errors
    let code = r#"
fn may_fail(x) -> Result<int, str>:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    result = may_fail(x)?  # If Err, early return with the error
    return Ok(result + 1)

res = caller(5)
main = res.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    // 5 * 2 = 10, then + 1 = 11
    assert_eq!(result.exit_code, 11);
}

#[test]
fn interpreter_question_mark_propagates_error() {
    // ? operator propagates the error to caller
    let code = r#"
fn may_fail(x) -> Result<int, str>:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    result = may_fail(x)?
    return Ok(result + 1)

res = caller(-5)  # Will return Err("negative")
main = res.unwrap_or(-99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -99);
}

#[test]
fn interpreter_question_mark_chained() {
    // Multiple ? operators in chain
    let code = r#"
fn step1(x):
    if x < 0:
        return Err("step1 failed")
    return Ok(x + 10)

fn step2(x):
    if x > 100:
        return Err("step2 failed")
    return Ok(x * 2)

fn pipeline(x):
    a = step1(x)?
    b = step2(a)?
    return Ok(b)

res = pipeline(5)
main = res.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    // 5 + 10 = 15, 15 * 2 = 30
    assert_eq!(result.exit_code, 30);
}

// ============= Match Guards (#74) =============
// Match guards allow conditional patterns: case x if condition:

#[test]
fn interpreter_match_guard_basic() {
    // Basic match guard with if condition
    let code = r#"
fn classify(x):
    match x:
        n if n < 0 =>
            return -1
        n if n == 0 =>
            return 0
        n if n > 0 =>
            return 1
    return -99

main = classify(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_guard_negative() {
    let code = r#"
fn classify(x):
    match x:
        n if n < 0 =>
            return -1
        n if n == 0 =>
            return 0
        n if n > 0 =>
            return 1
    return -99

main = classify(-10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -1);
}

#[test]
fn interpreter_match_guard_uses_binding() {
    // Guard can use the bound variable
    let code = r#"
fn verify(pair):
    match pair:
        (a, b) if a + b > 10 =>
            return 1
        (a, b) if a + b == 10 =>
            return 0
        _ =>
            return -1
    return -99

main = verify((7, 5))  # 7 + 5 = 12 > 10
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_guard_fallthrough() {
    // When guard fails, try next arm
    let code = r#"
fn test(x):
    match x:
        n if n > 100 =>
            return 100
        n if n > 10 =>
            return 10
        n =>
            return n
    return -99

main = test(50)  # 50 > 100? No. 50 > 10? Yes -> return 10
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

// ============= If Let / While Let (#75) =============
// Pattern matching in conditionals: if let pattern = expr:

#[test]
fn interpreter_if_let_some() {
    // If let with Option/Some pattern
    let code = r#"
opt = Some(42)
var res = 0
if let Some(x) = opt:
    res = x
main = res
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_if_let_none_else() {
    // If let with else branch for non-matching
    let code = r#"
opt = None
var res = 0
if let Some(x) = opt:
    res = x
else:
    res = -1
main = res
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, -1);
}

#[test]
fn interpreter_if_let_ok() {
    // If let with Result/Ok pattern
    let code = r#"
res = Ok(100)
var output = 0
if let Ok(value) = res:
    output = value
main = output
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_while_let_basic() {
    // While let loop that extracts values
    let code = r#"
fn next_item(n):
    if n > 0:
        return Some(n)
    return None

var counter = 3
var sum = 0
while let Some(value) = next_item(counter):
    sum = sum + value
    counter = counter - 1
main = sum  # 3 + 2 + 1 = 6
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

// ============= Or Patterns (#80) =============
// Match multiple patterns with |

#[test]
fn interpreter_or_pattern_basic() {
    // Match multiple literal values
    let code = r#"
fn classify(x):
    match x:
        1 | 2 | 3 =>
            return 1  # small
        4 | 5 | 6 =>
            return 2  # medium
        _ =>
            return 3  # large

main = classify(2)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // 2 matches first group
}

#[test]
fn interpreter_or_pattern_medium() {
    let code = r#"
fn classify(x):
    match x:
        1 | 2 | 3 =>
            return 1  # small
        4 | 5 | 6 =>
            return 2  # medium
        _ =>
            return 3  # large

main = classify(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2); // 5 matches second group
}

#[test]
fn interpreter_or_pattern_with_wildcard() {
    let code = r#"
fn verify(x):
    match x:
        0 | 1 =>
            return 10
        _ =>
            return 99

main = verify(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

// ============= Range Patterns (#81) =============
// Match a range of values with .. or ..=

#[test]
fn interpreter_range_pattern_exclusive() {
    // Exclusive range 0..10 (includes 0-9)
    let code = r#"
fn classify(x):
    match x:
        0..10 =>
            return 1
        10..20 =>
            return 2
        _ =>
            return 3

main = classify(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_range_pattern_exclusive_boundary() {
    // Test that exclusive range doesn't include end
    let code = r#"
fn classify(x):
    match x:
        0..10 =>
            return 1
        10..20 =>
            return 2
        _ =>
            return 3

main = classify(10)  # 10 is not in 0..10, but is in 10..20
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_range_pattern_inclusive() {
    // Inclusive range 0..=10 (includes 0-10)
    let code = r#"
fn classify(x):
    match x:
        0..=5 =>
            return 1
        6..=10 =>
            return 2
        _ =>
            return 3

main = classify(5)  # 5 is in 0..=5
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// Note: Negative number patterns like -10..0 are not supported yet
// as the pattern parser doesn't handle unary minus

// ============= Hexadecimal Literals (#93) =============

#[test]
fn interpreter_hex_literal() {
    let code = r#"
x = 0xFF
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 255);
}

#[test]
fn interpreter_hex_arithmetic() {
    let code = r#"
x = 0x10 + 0x20
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 48); // 16 + 32 = 48
}

// ============= Binary Literals (#94) =============

#[test]
fn interpreter_binary_literal() {
    let code = r#"
x = 0b1010
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_binary_with_underscores() {
    let code = r#"
x = 0b1111_0000
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 240);
}

// ============= Octal Literals (#95) =============

#[test]
fn interpreter_octal_literal() {
    let code = r#"
x = 0o755
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 493); // 7*64 + 5*8 + 5 = 493
}
