//! JIT compilation tests

use simple_driver::run_jit;

#[test]
fn jit_simple_return() {
    let code = r#"
fn main() -> i64:
    return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_arithmetic_add() {
    let code = r#"
fn main() -> i64:
    return 10 + 32
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_arithmetic_sub() {
    let code = r#"
fn main() -> i64:
    return 50 - 8
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_arithmetic_mul() {
    let code = r#"
fn main() -> i64:
    return 6 * 7
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_arithmetic_div() {
    let code = r#"
fn main() -> i64:
    return 84 / 2
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_arithmetic_mod() {
    let code = r#"
fn main() -> i64:
    return 142 % 100
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_negation() {
    let code = r#"
fn main() -> i64:
    return -(-42)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_complex_expression() {
    let code = r#"
fn main() -> i64:
    return (10 + 5) * 3 - 3
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_function_call() {
    let code = r#"
fn double(x: i64) -> i64:
    return x * 2

fn main() -> i64:
    return double(21)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_multiple_function_calls() {
    let code = r#"
fn add(a: i64, b: i64) -> i64:
    return a + b

fn mul(a: i64, b: i64) -> i64:
    return a * b

fn main() -> i64:
    return add(mul(6, 7), 0)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_conditional_if_true() {
    let code = r#"
fn main() -> i64:
    if 1 > 0:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_conditional_if_false() {
    let code = r#"
fn main() -> i64:
    if 0 > 1:
        return 0
    else:
        return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_comparison_lt() {
    let code = r#"
fn main() -> i64:
    if 5 < 10:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_comparison_eq() {
    let code = r#"
fn main() -> i64:
    if 42 == 42:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_recursive_factorial() {
    let code = r#"
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)

fn main() -> i64:
    return factorial(5)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 120);
}

#[test]
fn jit_recursive_fibonacci() {
    let code = r#"
fn fib(n: i64) -> i64:
    if n <= 1:
        return n
    else:
        return fib(n - 1) + fib(n - 2)

fn main() -> i64:
    return fib(10)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 55);
}

#[test]
fn jit_bitwise_and() {
    let code = r#"
fn main() -> i64:
    return 0xFF & 0x2A
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_bitwise_or() {
    let code = r#"
fn main() -> i64:
    return 0x20 | 0x0A
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_bitwise_xor() {
    let code = r#"
fn main() -> i64:
    return 0x55 ^ 0x7F
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_shift_left() {
    let code = r#"
fn main() -> i64:
    return 21 << 1
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_shift_right() {
    let code = r#"
fn main() -> i64:
    return 84 >> 1
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Feature #2: Variables & Let Bindings
// =============================================================================

#[test]
fn jit_let_binding_simple() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 42
    return x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_let_binding_expression() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 10 + 32
    return x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_multiple_let_bindings() {
    let code = r#"
fn main() -> i64:
    let a: i64 = 6
    let b: i64 = 7
    return a * b
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_let_binding_chain() {
    let code = r#"
fn main() -> i64:
    let a: i64 = 10
    let b: i64 = a + 5
    let c: i64 = b * 2
    let d: i64 = c + 12
    return d
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_mutable_variable() {
    let code = r#"
fn main() -> i64:
    let mut x: i64 = 0
    x = 42
    return x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_mutable_increment() {
    let code = r#"
fn main() -> i64:
    let mut x: i64 = 40
    x = x + 2
    return x
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Feature #6: Loops (while)
// =============================================================================

#[test]
fn jit_while_loop_simple() {
    let code = r#"
fn main() -> i64:
    let mut i: i64 = 0
    while i < 42:
        i = i + 1
    return i
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_while_loop_sum() {
    let code = r#"
fn main() -> i64:
    let mut sum: i64 = 0
    let mut i: i64 = 1
    while i <= 9:
        sum = sum + i
        i = i + 1
    return sum
"#;
    let result = run_jit(code).unwrap();
    // Sum of 1..9 = 45, but we want 42 so let's adjust
    assert_eq!(result.exit_code, 45);
}

#[test]
fn jit_while_loop_countdown() {
    let code = r#"
fn main() -> i64:
    let mut n: i64 = 10
    let mut result: i64 = 0
    while n > 0:
        result = result + n
        n = n - 1
    return result
"#;
    let result = run_jit(code).unwrap();
    // Sum of 10..1 = 55
    assert_eq!(result.exit_code, 55);
}

#[test]
fn jit_nested_while_loops() {
    let code = r#"
fn main() -> i64:
    let mut result: i64 = 0
    let mut i: i64 = 0
    while i < 6:
        let mut j: i64 = 0
        while j < 7:
            result = result + 1
            j = j + 1
        i = i + 1
    return result
"#;
    let result = run_jit(code).unwrap();
    // 6 * 7 = 42
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Feature #4: Logical Operators
// =============================================================================

#[test]
fn jit_logical_and_true() {
    let code = r#"
fn main() -> i64:
    if 1 > 0 and 2 > 1:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_logical_and_false() {
    let code = r#"
fn main() -> i64:
    if 1 > 0 and 0 > 1:
        return 0
    else:
        return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_logical_or_true() {
    let code = r#"
fn main() -> i64:
    if 0 > 1 or 1 > 0:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_logical_or_false() {
    let code = r#"
fn main() -> i64:
    if 0 > 1 or 0 > 2:
        return 0
    else:
        return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_comparison_not_equal() {
    let code = r#"
fn main() -> i64:
    if 41 != 42:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_comparison_lte() {
    let code = r#"
fn main() -> i64:
    if 42 <= 42:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_comparison_gte() {
    let code = r#"
fn main() -> i64:
    if 42 >= 42:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Feature #93-95: Hex, Binary, Octal Literals
// =============================================================================

#[test]
fn jit_hex_literal() {
    let code = r#"
fn main() -> i64:
    return 0x2A
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_hex_literal_uppercase() {
    let code = r#"
fn main() -> i64:
    return 0X2A
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_binary_literal() {
    let code = r#"
fn main() -> i64:
    return 0b101010
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_binary_literal_uppercase() {
    let code = r#"
fn main() -> i64:
    return 0B101010
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_octal_literal() {
    let code = r#"
fn main() -> i64:
    return 0o52
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_octal_literal_uppercase() {
    let code = r#"
fn main() -> i64:
    return 0O52
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_hex_in_expression() {
    let code = r#"
fn main() -> i64:
    return 0x20 + 0x0A
"#;
    let result = run_jit(code).unwrap();
    // 0x20 = 32, 0x0A = 10, sum = 42
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_binary_in_expression() {
    let code = r#"
fn main() -> i64:
    return 0b100000 + 0b1010
"#;
    let result = run_jit(code).unwrap();
    // 0b100000 = 32, 0b1010 = 10, sum = 42
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Feature #5: Control Flow (if/elif/else)
// =============================================================================

#[test]
fn jit_if_elif_else_first() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 1
    if x == 1:
        return 42
    elif x == 2:
        return 0
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_if_elif_else_second() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 2
    if x == 1:
        return 0
    elif x == 2:
        return 42
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_if_elif_else_third() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 3
    if x == 1:
        return 0
    elif x == 2:
        return 0
    else:
        return 42
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_nested_if() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 10
    let y: i64 = 5
    if x > 5:
        if y > 3:
            return 42
        else:
            return 0
    else:
        return 0
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

// =============================================================================
// Integration Tests: Complex Programs
// =============================================================================

#[test]
fn jit_gcd() {
    let code = r#"
fn gcd(a: i64, b: i64) -> i64:
    if b == 0:
        return a
    else:
        return gcd(b, a % b)

fn main() -> i64:
    return gcd(84, 126)
"#;
    let result = run_jit(code).unwrap();
    // GCD(84, 126) = 42
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_sum_of_squares() {
    let code = r#"
fn square(x: i64) -> i64:
    return x * x

fn sum_squares(n: i64) -> i64:
    if n <= 0:
        return 0
    else:
        return square(n) + sum_squares(n - 1)

fn main() -> i64:
    return sum_squares(4)
"#;
    let result = run_jit(code).unwrap();
    // 1 + 4 + 9 + 16 = 30
    assert_eq!(result.exit_code, 30);
}

#[test]
fn jit_iterative_power() {
    let code = r#"
fn power(base: i64, exp: i64) -> i64:
    let mut result: i64 = 1
    let mut i: i64 = 0
    while i < exp:
        result = result * base
        i = i + 1
    return result

fn main() -> i64:
    return power(2, 5) + 10
"#;
    let result = run_jit(code).unwrap();
    // 2^5 = 32, 32 + 10 = 42
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_is_even_odd() {
    let code = r#"
fn is_even(n: i64) -> i64:
    if n % 2 == 0:
        return 1
    else:
        return 0

fn main() -> i64:
    let a: i64 = is_even(42)
    let b: i64 = is_even(41)
    return a * 42 + b * 0
"#;
    let result = run_jit(code).unwrap();
    // is_even(42) = 1, is_even(41) = 0
    // 1 * 42 + 0 * 0 = 42
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_abs() {
    let code = r#"
fn abs(x: i64) -> i64:
    if x < 0:
        return -x
    else:
        return x

fn main() -> i64:
    return abs(-42)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn jit_max_of_three() {
    let code = r#"
fn max(a: i64, b: i64) -> i64:
    if a > b:
        return a
    else:
        return b

fn max3(a: i64, b: i64, c: i64) -> i64:
    return max(max(a, b), c)

fn main() -> i64:
    return max3(10, 42, 30)
"#;
    let result = run_jit(code).unwrap();
    assert_eq!(result.exit_code, 42);
}
