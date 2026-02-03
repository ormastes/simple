//! JIT compilation tests
//!
//! Uses `backend_test!` macro to generate per-backend tests.
//! Tests marked `interp_jit` run on both Interpreter and JIT.
//! Tests that previously had `#[ignore]` due to JIT SIGSEGV on ==/!=
//! are now `interp` only (still tested on interpreter, JIT skipped).

mod test_helpers;

// =============================================================================
// Feature #1: Arithmetic & Expressions
// =============================================================================

backend_test!(
    jit_simple_return,
    interp_jit,
    r#"
fn main() -> i64:
    return 42
"#,
    42
);

backend_test!(
    jit_arithmetic_add,
    interp_jit,
    r#"
fn main() -> i64:
    return 10 + 32
"#,
    42
);

backend_test!(
    jit_arithmetic_sub,
    interp_jit,
    r#"
fn main() -> i64:
    return 50 - 8
"#,
    42
);

backend_test!(
    jit_arithmetic_mul,
    interp_jit,
    r#"
fn main() -> i64:
    return 6 * 7
"#,
    42
);

backend_test!(
    jit_arithmetic_div,
    interp_jit,
    r#"
fn main() -> i64:
    return 84 / 2
"#,
    42
);

backend_test!(
    jit_arithmetic_mod,
    interp_jit,
    r#"
fn main() -> i64:
    return 142 % 100
"#,
    42
);

backend_test!(
    jit_negation,
    interp_jit,
    r#"
fn main() -> i64:
    return -(-42)
"#,
    42
);

backend_test!(
    jit_complex_expression,
    interp_jit,
    r#"
fn main() -> i64:
    return (10 + 5) * 3 - 3
"#,
    42
);

backend_test!(
    jit_function_call,
    interp_jit,
    r#"
fn double(x: i64) -> i64:
    return x * 2

fn main() -> i64:
    return double(21)
"#,
    42
);

backend_test!(
    jit_multiple_function_calls,
    interp_jit,
    r#"
fn add(a: i64, b: i64) -> i64:
    return a + b

fn mul(a: i64, b: i64) -> i64:
    return a * b

fn main() -> i64:
    return add(mul(6, 7), 0)
"#,
    42
);

backend_test!(
    jit_conditional_if_true,
    interp_jit,
    r#"
fn main() -> i64:
    if 1 > 0:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    jit_conditional_if_false,
    interp_jit,
    r#"
fn main() -> i64:
    if 0 > 1:
        return 0
    else:
        return 42
"#,
    42
);

backend_test!(
    jit_comparison_lt,
    interp_jit,
    r#"
fn main() -> i64:
    if 5 < 10:
        return 42
    else:
        return 0
"#,
    42
);

// FIXME: SIGSEGV crash in JIT compiler when handling == comparison
backend_test!(
    jit_comparison_eq,
    interp,
    r#"
fn main() -> i64:
    if 42 == 42:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    jit_recursive_factorial,
    interp_jit,
    r#"
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)

fn main() -> i64:
    return factorial(5)
"#,
    120
);

backend_test!(
    jit_recursive_fibonacci,
    interp_jit,
    r#"
fn fib(n: i64) -> i64:
    if n <= 1:
        return n
    else:
        return fib(n - 1) + fib(n - 2)

fn main() -> i64:
    return fib(10)
"#,
    55
);

backend_test!(
    jit_bitwise_and,
    interp_jit,
    r#"
fn main() -> i64:
    return 0xFF & 0x2A
"#,
    42
);

backend_test!(
    jit_bitwise_or,
    interp_jit,
    r#"
fn main() -> i64:
    return 0x20 | 0x0A
"#,
    42
);

backend_test!(
    jit_bitwise_xor,
    interp_jit,
    r#"
fn main() -> i64:
    return 0x55 xor 0x7F
"#,
    42
);

backend_test!(
    jit_shift_left,
    interp_jit,
    r#"
fn main() -> i64:
    return 21 << 1
"#,
    42
);

backend_test!(
    jit_shift_right,
    interp_jit,
    r#"
fn main() -> i64:
    return 84 >> 1
"#,
    42
);

// =============================================================================
// Feature #2: Variables & Let Bindings
// =============================================================================

backend_test!(
    jit_let_binding_simple,
    interp_jit,
    r#"
fn main() -> i64:
    let x: i64 = 42
    return x
"#,
    42
);

backend_test!(
    jit_let_binding_expression,
    interp_jit,
    r#"
fn main() -> i64:
    let x: i64 = 10 + 32
    return x
"#,
    42
);

backend_test!(
    jit_multiple_let_bindings,
    interp_jit,
    r#"
fn main() -> i64:
    let a: i64 = 6
    let b: i64 = 7
    return a * b
"#,
    42
);

backend_test!(
    jit_let_binding_chain,
    interp_jit,
    r#"
fn main() -> i64:
    let a: i64 = 10
    let b: i64 = a + 5
    let c: i64 = b * 2
    let d: i64 = c + 12
    return d
"#,
    42
);

backend_test!(
    jit_mutable_variable,
    interp_jit,
    r#"
fn main() -> i64:
    let mut x: i64 = 0
    x = 42
    return x
"#,
    42
);

backend_test!(
    jit_mutable_increment,
    interp_jit,
    r#"
fn main() -> i64:
    let mut x: i64 = 40
    x = x + 2
    return x
"#,
    42
);

// =============================================================================
// Feature #6: Loops (while)
// =============================================================================

backend_test!(
    jit_while_loop_simple,
    interp_jit,
    r#"
fn main() -> i64:
    let mut i: i64 = 0
    while i < 42:
        i = i + 1
    return i
"#,
    42
);

backend_test!(
    jit_while_loop_sum,
    interp_jit,
    r#"
fn main() -> i64:
    let mut sum: i64 = 0
    let mut i: i64 = 1
    while i <= 9:
        sum = sum + i
        i = i + 1
    return sum
"#,
    45
);

backend_test!(
    jit_while_loop_countdown,
    interp_jit,
    r#"
fn main() -> i64:
    let mut n: i64 = 10
    let mut res: i64 = 0
    while n > 0:
        res = res + n
        n = n - 1
    return res
"#,
    55
);

backend_test!(
    jit_nested_while_loops,
    interp_jit,
    r#"
fn main() -> i64:
    let mut res: i64 = 0
    let mut i: i64 = 0
    while i < 6:
        let mut j: i64 = 0
        while j < 7:
            res = res + 1
            j = j + 1
        i = i + 1
    return res
"#,
    42
);

// =============================================================================
// Feature #4: Logical Operators
// =============================================================================

backend_test!(
    jit_logical_and_true,
    interp_jit,
    r#"
fn main() -> i64:
    if 1 > 0 and 2 > 1:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    jit_logical_and_false,
    interp_jit,
    r#"
fn main() -> i64:
    if 1 > 0 and 0 > 1:
        return 0
    else:
        return 42
"#,
    42
);

backend_test!(
    jit_logical_or_true,
    interp_jit,
    r#"
fn main() -> i64:
    if 0 > 1 or 1 > 0:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    jit_logical_or_false,
    interp_jit,
    r#"
fn main() -> i64:
    if 0 > 1 or 0 > 2:
        return 0
    else:
        return 42
"#,
    42
);

// FIXME: SIGSEGV crash in JIT compiler when handling != comparison
backend_test!(
    jit_comparison_not_equal,
    interp,
    r#"
fn main() -> i64:
    if 41 != 42:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    jit_comparison_lte,
    interp_jit,
    r#"
fn main() -> i64:
    if 42 <= 42:
        return 42
    else:
        return 0
"#,
    42
);

backend_test!(
    jit_comparison_gte,
    interp_jit,
    r#"
fn main() -> i64:
    if 42 >= 42:
        return 42
    else:
        return 0
"#,
    42
);

// =============================================================================
// Feature #93-95: Hex, Binary, Octal Literals
// =============================================================================

backend_test!(
    jit_hex_literal,
    interp_jit,
    r#"
fn main() -> i64:
    return 0x2A
"#,
    42
);

backend_test!(
    jit_hex_literal_uppercase,
    interp_jit,
    r#"
fn main() -> i64:
    return 0X2A
"#,
    42
);

backend_test!(
    jit_binary_literal,
    interp_jit,
    r#"
fn main() -> i64:
    return 0b101010
"#,
    42
);

backend_test!(
    jit_binary_literal_uppercase,
    interp_jit,
    r#"
fn main() -> i64:
    return 0B101010
"#,
    42
);

backend_test!(
    jit_octal_literal,
    interp_jit,
    r#"
fn main() -> i64:
    return 0o52
"#,
    42
);

backend_test!(
    jit_octal_literal_uppercase,
    interp_jit,
    r#"
fn main() -> i64:
    return 0O52
"#,
    42
);

backend_test!(
    jit_hex_in_expression,
    interp_jit,
    r#"
fn main() -> i64:
    return 0x20 + 0x0A
"#,
    42
);

backend_test!(
    jit_binary_in_expression,
    interp_jit,
    r#"
fn main() -> i64:
    return 0b100000 + 0b1010
"#,
    42
);

// =============================================================================
// Feature #5: Control Flow (if/elif/else)
// =============================================================================

// FIXME: SIGSEGV crash - uses == comparison which crashes in JIT
backend_test!(
    jit_if_elif_else_first,
    interp,
    r#"
fn main() -> i64:
    let x: i64 = 1
    if x == 1:
        return 42
    elif x == 2:
        return 0
    else:
        return 0
"#,
    42
);

// FIXME: SIGSEGV crash - uses == comparison which crashes in JIT
backend_test!(
    jit_if_elif_else_second,
    interp,
    r#"
fn main() -> i64:
    let x: i64 = 2
    if x == 1:
        return 0
    elif x == 2:
        return 42
    else:
        return 0
"#,
    42
);

// FIXME: SIGSEGV crash - uses == comparison which crashes in JIT
backend_test!(
    jit_if_elif_else_third,
    interp,
    r#"
fn main() -> i64:
    let x: i64 = 3
    if x == 1:
        return 0
    elif x == 2:
        return 0
    else:
        return 42
"#,
    42
);

backend_test!(
    jit_nested_if,
    interp_jit,
    r#"
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
"#,
    42
);

// =============================================================================
// Integration Tests: Complex Programs
// =============================================================================

// FIXME: SIGSEGV crash - uses == comparison which crashes in JIT
backend_test!(
    jit_gcd,
    interp,
    r#"
fn gcd(a: i64, b: i64) -> i64:
    if b == 0:
        return a
    else:
        return gcd(b, a % b)

fn main() -> i64:
    return gcd(84, 126)
"#,
    42
);

backend_test!(
    jit_sum_of_squares,
    interp_jit,
    r#"
fn square(x: i64) -> i64:
    return x * x

fn sum_squares(n: i64) -> i64:
    if n <= 0:
        return 0
    else:
        return square(n) + sum_squares(n - 1)

fn main() -> i64:
    return sum_squares(4)
"#,
    30
);

backend_test!(
    jit_iterative_power,
    interp_jit,
    r#"
fn power(base: i64, exp: i64) -> i64:
    let mut res: i64 = 1
    let mut i: i64 = 0
    while i < exp:
        res = res * base
        i = i + 1
    return res

fn main() -> i64:
    return power(2, 5) + 10
"#,
    42
);

// FIXME: SIGSEGV crash - uses == comparison which crashes in JIT
backend_test!(
    jit_is_even_odd,
    interp,
    r#"
fn is_even(n: i64) -> i64:
    if n % 2 == 0:
        return 1
    else:
        return 0

fn main() -> i64:
    let a: i64 = is_even(42)
    let b: i64 = is_even(41)
    return a * 42 + b * 0
"#,
    42
);

backend_test!(
    jit_abs,
    interp_jit,
    r#"
fn abs(x: i64) -> i64:
    if x < 0:
        return -x
    else:
        return x

fn main() -> i64:
    return abs(-42)
"#,
    42
);

backend_test!(
    jit_max_of_three,
    interp_jit,
    r#"
fn max(a: i64, b: i64) -> i64:
    if a > b:
        return a
    else:
        return b

fn max3(a: i64, b: i64, c: i64) -> i64:
    return max(max(a, b), c)

fn main() -> i64:
    return max3(10, 42, 30)
"#,
    42
);
