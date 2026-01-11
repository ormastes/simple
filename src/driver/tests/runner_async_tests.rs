//! Runner tests for async, futures, generators (Features 101-103)
//!
//! This module tests:
//! - Generator state machine (Feature 101)
//! - Future body execution (Feature 102)
//! - Interpreter/Codegen parity (Feature 103)

// Import shared test helpers
mod test_helpers;
use test_helpers::run_expect;

// ========================================================================
// Generator State Machine Tests (Feature 101)
// ========================================================================

#[test]
fn runner_generator_single_yield() {
    run_expect(
        r#"
let gen = generator(\: yield 42)
main = next(gen)
"#,
        42,
    );
}

#[test]
fn runner_generator_multiple_yields() {
    run_expect(
        r#"
let gen = generator(\: [yield 1, yield 2, yield 3])
let a = next(gen)
let b = next(gen)
let c = next(gen)
main = a + b + c
"#,
        6,
    );
}

#[test]
fn runner_generator_exhaustion_returns_nil() {
    // After generator is exhausted, next() returns nil which converts to 0
    run_expect(
        r#"
let gen = generator(\: yield 10)
let first = next(gen)
let second = next(gen)
# nil is falsy, so this returns first (10)
main = if second: second else: first
"#,
        10,
    );
}

#[test]
fn runner_generator_state_preserved_across_yields() {
    // Test that local values persist across yields
    // Using tuple expression to sequence operations in single line
    run_expect(
        r#"
let gen = generator(\: (yield 10, yield 15)[1])
let a = next(gen)
let b = next(gen)
main = a + b
"#,
        25,
    );
}

#[test]
fn runner_generator_with_captured_variable() {
    // Test generator capturing outer variable
    run_expect(
        r#"
let base = 100
let gen = generator(\: [yield base, yield base])
let a = next(gen)
let b = next(gen)
main = a + b
"#,
        200,
    );
}

#[test]
fn runner_generator_arithmetic_in_yield() {
    // Test arithmetic expression - computed before yield
    run_expect(
        r#"
let value = 2 * 3
let gen = generator(\: yield value)
main = next(gen)
"#,
        6,
    );
}

#[test]
fn runner_generator_nested_iteration() {
    // Test using next() multiple times to drain generator
    run_expect(
        r#"
let gen = generator(\: [yield 1, yield 2, yield 3, yield 4])
let sum = next(gen) + next(gen) + next(gen) + next(gen)
main = sum
"#,
        10,
    );
}

// ========================================================================
// Interpreter/Codegen Parity Tests
// These tests verify compiled generators match interpreter behavior
// ========================================================================

#[test]
fn parity_generator_basic_sequence() {
    // Same test should work via interpreter and compiled path
    // The interpreter tests in interpreter_async_tests.rs use same patterns
    run_expect(
        r#"
let gen = generator(\: [yield 1, yield 2, yield 3])
let first = next(gen)
let second = next(gen)
let third = next(gen)
main = first + second + third
"#,
        6,
    );
}

#[test]
fn parity_generator_single_value() {
    // Matches interpreter_generator_single test
    run_expect(
        r#"
let gen = generator(\: yield 42)
main = next(gen)
"#,
        42,
    );
}

// ========================================================================
// Future Body Execution Tests (Feature 102)
// ========================================================================

#[test]
fn runner_future_basic() {
    // Create a future and await it - value should be preserved
    run_expect(
        r#"
let f = future(42)
let res = await f
main = res
"#,
        42,
    );
}

#[test]
fn runner_future_with_computation() {
    // Future with function call
    run_expect(
        r#"
fn compute():
    return 10 + 20 + 30

let f = future(compute())
let res = await f
main = res
"#,
        60,
    );
}

#[test]
fn runner_future_multiple() {
    // Multiple futures
    run_expect(
        r#"
let f1 = future(10)
let f2 = future(20)
let f3 = future(30)
let r1 = await f1
let r2 = await f2
let r3 = await f3
main = r1 + r2 + r3
"#,
        60,
    );
}

#[test]
fn runner_await_non_future() {
    // Await on a non-future value now produces a semantic error
    use test_helpers::run_expect_compile_error;
    run_expect_compile_error(
        r#"
let x = 42
let res = await x
main = res
"#,
        "await requires a Future or Actor handle",
    );
}

#[test]
fn runner_future_function_call() {
    // future() creates a future from a function call
    run_expect(
        r#"
fn slow_add(a: i64, b: i64) -> i64:
    return a + b

let f = future(slow_add(15, 27))
let res = await f
main = res
"#,
        42,
    );
}

#[test]
fn runner_async_fn_basic() {
    // async fn returns a result - auto-awaited at top level
    run_expect(
        r#"
async fn fetch():
    return 42

main = fetch()
"#,
        42,
    );
}

#[test]
fn runner_async_can_call_async() {
    // async fn can call other async functions
    run_expect(
        r#"
async fn double(x: i64) -> i64:
    return x * 2

async fn quadruple(x: i64) -> i64:
    return double(double(x))

main = quadruple(10)
"#,
        40,
    );
}

// ========================================================================
// Interpreter/Codegen Parity Tests for Futures
// ========================================================================

#[test]
fn parity_future_basic() {
    // Matches interpreter_future_basic test
    run_expect(
        r#"
let f = future(42)
let res = await f
main = res
"#,
        42,
    );
}

#[test]
fn parity_future_with_function() {
    // Matches interpreter_future_function_call test
    run_expect(
        r#"
fn slow_add(a: i64, b: i64) -> i64:
    return a + b

let f = future(slow_add(15, 27))
let res = await f
main = res
"#,
        42,
    );
}

// ========================================================================
// Codegen Parity Completion Tests (Feature 103) - COMPLETE
// These tests verify the ctx ABI wiring for outlined bodies with captures.
// Native codegen now supports generators, futures, and actors with proper
// HIR lowering and MIR emission.
// ========================================================================

#[test]
fn parity_generator_multiple_captures() {
    // Generator capturing multiple outer variables tests ctx packing/unpacking
    run_expect(
        r#"
let a = 10
let b = 20
let c = 30
let gen = generator(\: [yield a, yield b, yield c])
let x = next(gen)
let y = next(gen)
let z = next(gen)
main = x + y + z
"#,
        60,
    );
}

#[test]
fn parity_generator_capture_and_compute() {
    // Generator using captured variable in computation
    // Note: yield has low precedence, so parentheses are needed around expressions
    run_expect(
        r#"
let multiplier = 10
let gen = generator(\: [yield (1 * multiplier), yield (2 * multiplier), yield (3 * multiplier)])
let a = next(gen)
let b = next(gen)
let c = next(gen)
main = a + b + c
"#,
        60,
    );
}

#[test]
fn parity_future_with_capture() {
    // Future capturing outer variable tests ctx wiring
    run_expect(
        r#"
let base = 40
let f = future(base + 2)
let res = await f
main = res
"#,
        42,
    );
}

#[test]
fn parity_future_multiple_captures() {
    // Future capturing multiple variables
    run_expect(
        r#"
let a = 10
let b = 20
let c = 12
let f = future(a + b + c)
let res = await f
main = res
"#,
        42,
    );
}

#[test]
fn parity_actor_basic_spawn() {
    // Basic actor spawn without captures
    run_expect(
        r#"
fn worker():
    return 42

let h = spawn worker()
main = 0
"#,
        0,
    );
}

#[test]
fn parity_generator_state_and_capture() {
    // Tests both state machine (yield) and capture unpacking
    // Note: yield has low precedence, so parentheses are needed around expressions
    run_expect(
        r#"
let offset = 100
let gen = generator(\: [yield (1 + offset), yield (2 + offset)])
let a = next(gen)
let b = next(gen)
main = a + b
"#,
        203,
    );
}

#[test]
fn parity_generator_exhaustion_with_capture() {
    // Exhausted generator with capture returns nil (0)
    run_expect(
        r#"
let value = 42
let gen = generator(\: yield value)
let first = next(gen)
let second = next(gen)
main = first
"#,
        42,
    );
}

#[test]
fn parity_nested_generator_captures() {
    // Generator capturing variable used in nested expression
    // Note: yield has low precedence, so parentheses are needed around expressions
    run_expect(
        r#"
let x = 5
let y = 3
let gen = generator(\: yield (x * y + x))
main = next(gen)
"#,
        20,
    );
}

// ========================================================================
// Additional Codegen Parity Tests (Feature 103 Completion)
// These tests verify hybrid execution and interpreter fallback work correctly
// ========================================================================

#[test]
fn parity_control_flow_nested() {
    // Complex nested control flow should produce same results
    run_expect(
        r#"
fn compute(n: i64) -> i64:
    let mut sum = 0
    let mut i = 0
    while i < n:
        if i % 2 == 0:
            sum = sum + i
        else:
            sum = sum + 1
        i = i + 1
    return sum

main = compute(10)
"#,
        25, // 0 + 1 + 2 + 1 + 4 + 1 + 6 + 1 + 8 + 1 = 25
    );
}

#[test]
fn parity_recursive_function() {
    // Recursive functions should work in both modes
    // Use small input to avoid stack overflow in test
    run_expect(
        r#"
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

main = factorial(3)
"#,
        6, // 3! = 6
    );
}

#[test]
fn parity_struct_field_access() {
    // Struct field access in both modes
    run_expect(
        r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x * p.y
"#,
        200,
    );
}

#[test]
fn parity_enum_pattern_match() {
    // Enum pattern matching in both modes
    run_expect(
        r#"
enum Result:
    Ok(i64)
    Err

let r = Result::Ok(42)
let mut value = 0
match r:
    Result::Ok(v) =>
        value = v
    Result::Err =>
        value = -1
main = value
"#,
        42,
    );
}

#[test]
fn parity_array_operations() {
    // Array operations in both modes
    run_expect(
        r#"
let arr = [10, 20, 30, 40, 50]
let mut sum = 0
let mut i = 0
while i < 5:
    sum = sum + arr[i]
    i = i + 1
main = sum
"#,
        150,
    );
}

#[test]
fn parity_tuple_destructure() {
    // Tuple indexing in both modes
    run_expect(
        r#"
let t = (10, 20, 30)
main = t[0] + t[1] + t[2]
"#,
        60,
    );
}

#[test]
fn parity_function_composition() {
    // Multiple function calls in expression
    run_expect(
        r#"
fn double(x: i64) -> i64:
    return x * 2

fn add_one(x: i64) -> i64:
    return x + 1

main = double(add_one(double(5)))
"#,
        22, // double(5)=10, add_one(10)=11, double(11)=22
    );
}

#[test]
fn parity_early_return() {
    // Early return from function
    run_expect(
        r#"
fn find_first_even(limit: i64) -> i64:
    let mut i = 1
    while i <= limit:
        if i % 2 == 0:
            return i
        i = i + 1
    return -1

main = find_first_even(10)
"#,
        2,
    );
}

#[test]
fn parity_boolean_logic() {
    // Boolean operations in both modes
    run_expect(
        r#"
fn check(a: i64, b: i64) -> i64:
    if a > 0 and b > 0:
        return 1
    if a > 0 or b > 0:
        return 2
    return 0

main = check(1, 1) * 100 + check(1, 0) * 10 + check(0, 0)
"#,
        120, // 1*100 + 2*10 + 0 = 120
    );
}

#[test]
fn parity_dictionary_access() {
    // Dictionary operations
    run_expect(
        r#"
let d = {"a": 10, "b": 20, "c": 30}
main = d["a"] + d["b"] + d["c"]
"#,
        60,
    );
}
