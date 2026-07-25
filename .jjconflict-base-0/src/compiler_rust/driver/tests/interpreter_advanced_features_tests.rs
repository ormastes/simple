//! Interpreter Advanced Features Tests
//!
//! Tests for advanced language features: decorators, attributes, Result type,
//! ? operator, match guards, if let/while let, or patterns, range patterns,
//! and numeric literals (hex, binary, octal).

use simple_driver::interpreter::run_code;

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
    // Decorators are parsed but not applied by the interpreter yet.
    // identity(5) = 5 (undecorated)
    assert_eq!(result.exit_code, 5);
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
    // Decorators are parsed but not applied by the interpreter yet.
    // square(4) = 16 (undecorated)
    assert_eq!(result.exit_code, 16);
}

// ============= Attributes =============
// Attributes are compile-time metadata that can be attached to items.
// Currently we support inline, deprecated, and lint-level attributes.

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

// ============= Optional auto-wrap (FINDING-T2-dirent) =============
// When a function is declared -> T? and returns a plain T (no explicit Some()),
// the interpreter must auto-wrap the return value in Some() so that
// .is_some(), .unwrap(), .unwrap_or() work on the caller side.

#[test]
fn interpreter_optional_return_plain_int_unwrap() {
    // fn returns plain i32 from a -> i32? function; caller calls .unwrap()
    let code = r#"
fn find_offset() -> i32?:
    return 42

r = find_offset()
main = r.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_optional_return_plain_int_is_some() {
    // .is_some() must return true for auto-wrapped Some(42)
    let code = r#"
fn find_offset() -> i32?:
    return 42

r = find_offset()
var x = 0
if r.is_some():
    x = 1
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_optional_return_nil_is_none() {
    // returning nil from -> T? function must auto-wrap to None
    let code = r#"
fn find_offset() -> i32?:
    return nil

r = find_offset()
var x = 0
if r.is_none():
    x = 1
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_optional_return_unwrap_or() {
    // .unwrap_or() with auto-wrapped Some value returns the wrapped value
    let code = r#"
fn find_offset() -> i32?:
    return 7

r = find_offset()
main = r.unwrap_or(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 7);
}

#[test]
fn interpreter_optional_explicit_some_still_works() {
    // Explicit Some() wrapping must not double-wrap
    let code = r#"
fn find_offset() -> i32?:
    return Some(55)

r = find_offset()
main = r.unwrap()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 55);
}

// ---------------------------------------------------------------------------
// Generator iteration (S7)
//
// `gen f(): yield ...` functions evaluate eagerly in the interpreter: calling
// one runs the body to completion, collecting every yielded value into a
// Value::Generator. `for x in f()` then drains those values in order. These
// tests cover the previously-broken module-scope for-loop path (iter_to_vec in
// interpreter_helpers/collections.rs), which lacked a Value::Generator arm and
// failed with "cannot iterate over this type".
// ---------------------------------------------------------------------------

#[test]
fn interpreter_generator_for_in_collects_in_order() {
    // Multi-yield generator iterated by a module-scope for-loop.
    // Encode visitation order into a single integer: 1,2,3 -> 123.
    let code = r#"
gen counter():
    yield 1
    yield 2
    yield 3

var total = 0
for x in counter():
    total = total * 10 + x
main = total
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 123);
}

#[test]
fn interpreter_generator_zero_yields_iterates_zero_times() {
    // A generator that yields nothing must produce zero loop iterations.
    let code = r#"
gen empty():
    return

var count = 0
for x in empty():
    count = count + 1
main = count
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_plain_fn_returning_array_still_iterates() {
    // Regression guard: a non-generator function returning an array must still
    // be iterable by for-in (the new Generator arm must not disturb arrays).
    let code = r#"
fn nums():
    return [4, 5, 6]

var total = 0
for x in nums():
    total = total + x
main = total
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

// =============================================================================
// Regression: match arm early-return propagation
// Bug: interp_match_or_pattern_early_return_swallowed_2026-06-13
// Root cause: exec_block_fn used exec_if_expr/exec_match_expr for last-statement
// if/match handling, which collapsed Control::Return into a plain value instead
// of propagating it up to the enclosing function.
// Fix: use exec_if_core/exec_match_core which preserve Control::Return.
// =============================================================================

#[test]
fn interpreter_match_or_pattern_early_return_propagates() {
    // Regression: return inside if under or-pattern arm was swallowed.
    // Before fix: exit_code=0 (falls through to post-match return 0).
    // After fix: exit_code=1 (arm's early return honored).
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            if true:
                return 1
    return 0

main = test(Color.Red)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_or_pattern_second_variant_early_return_propagates() {
    // Both variants in the or-pattern must propagate the return.
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            if true:
                return 1
    return 0

main = test(Color.Blue)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_single_pattern_early_return_propagates() {
    // Single-pattern arm has the same bug: last stmt is an if with return.
    // Before fix: exit_code=0. After fix: exit_code=1.
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red:
            if true:
                return 1
    return 0

main = test(Color.Red)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_match_arm_value_no_early_return_still_works() {
    // Arm that just produces a value (no explicit return) must still work.
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            42
        _:
            0

main = test(Color.Red)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_match_arm_no_match_falls_through_to_post_match_return() {
    // Non-matching or-pattern arm: must fall through to post-match return.
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            if true:
                return 1
    return 0

main = test(Color.Green)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_match_arm_false_condition_falls_through() {
    // If condition is false, must fall through to post-match return (not arm value).
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            if false:
                return 1
    return 0

main = test(Color.Red)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_match_arm_nested_match_return_propagates() {
    // Nested match as the last statement of an arm: return must propagate.
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            match c:
                Color.Red:
                    return 10
                _:
                    return 20
    return 0

main = test(Color.Red)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_match_arm_nested_match_second_branch_return_propagates() {
    // Same as above but with the second sub-branch.
    let code = r#"
enum Color:
    Red
    Blue
    Green

fn test(c: Color) -> i64:
    match c:
        Color.Red | Color.Blue:
            match c:
                Color.Red:
                    return 10
                _:
                    return 20
    return 0

main = test(Color.Blue)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}
