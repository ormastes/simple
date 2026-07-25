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

backend_test!(
    jit_comparison_eq,
    interp_jit,
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

backend_test!(
    jit_comparison_not_equal,
    interp_jit,
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

backend_test!(
    jit_if_elif_else_first,
    interp_jit,
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

backend_test!(
    jit_if_elif_else_second,
    interp_jit,
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

backend_test!(
    jit_if_elif_else_third,
    interp_jit,
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

backend_test!(
    jit_gcd,
    interp_jit,
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

backend_test!(
    jit_is_even_odd,
    interp_jit,
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

// =============================================================================
// Task #170: `Result<i64,_>` Ok(v) payload extraction must not divide
// multiples-of-8 by 8 (deployed 2026-07-11 seed BoxInt<<3 tag-shift landmine).
//
// Root cause: MIR's extraction side (lowering_stmt.rs) has always assumed
// `rt_enum_payload` results are tagged and inserts UnboxInt (>>3) when
// storing into a concrete int/bool local -- exactly what a `case Ok(v):`
// bind, `?`, or `.unwrap()` does. Until commit 14922f8e3cb (2026-07-17,
// "flat-nullable unwrap + nested struct pattern in enum payload"),
// Some/Ok/Err construction (lowering_expr_call.rs) stored scalar payloads
// RAW (no <<3), so the extraction side's UnboxInt silently right-shifted a
// multiple-of-8 payload by 3 bits (48 -> 6, 8 -> 1, 64 -> 8) while leaving
// non-multiples of 8 apparently fine -- exactly the deployed 2026-07-11
// seed binary's symptom (that binary predates 14922f8e3cb, which fixes
// this by boxing scalars at all 6 Some/Ok/Err construction sites via
// box_enum_payload_if_needed()). These tests exercise construct+extract
// through the compiled JIT path (not just symbol relocation) so a
// reintroduced mismatch fails loudly on the actual returned value, across
// match-binding, `.unwrap()`, `?`, and if-val propagation forms. See
// doc/08_tracking/bug/task_170_result_ok_multiple_of_8_divide_verify_2026-07-17.md,
// doc/08_tracking/bug/native_result_unwrap_silent_wrong_161_2026-07-14.md,
// and doc/08_tracking/bug/seed_interp_flat_nullable_unwrap_wrong_value_2026-07-16.md
// for the fix commit and adjacent landmines in this same tag/box family.
//
// jit-only (not interp_jit): `RunningType::Interpreter` (the pure AST
// tree-walking backend reached via `Interpreter::run` in this test harness)
// SIGSEGVs on ANY `match <Result-returning call>(): case Ok(v): return v`
// construct -- reproduced independently with a minimal `Ok(1)` case, so it
// is a pre-existing, orthogonal interpreter-backend crash unrelated to the
// tag/box value bug this section regression-tests, not something to fix or
// paper over here. See
// doc/08_tracking/bug/interpreter_result_match_return_sigsegv_2026-07-17.md.
// =============================================================================

backend_test!(
    jit_result_ok_match_extraction_multiple_of_8,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(48)

fn main() -> i64:
    match get():
        case Ok(v):
            return v
        case Err(e):
            return -1
"#,
    48
);

backend_test!(
    jit_result_ok_match_extraction_small_multiple_of_8,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(8)

fn main() -> i64:
    match get():
        case Ok(v):
            return v
        case Err(e):
            return -1
"#,
    8
);

backend_test!(
    jit_result_ok_match_extraction_negative_multiple_of_8,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(-8)

fn main() -> i64:
    match get():
        case Ok(v):
            return v
        case Err(e):
            return -1
"#,
    -8
);

backend_test!(
    jit_result_ok_match_extraction_non_multiple_of_8_control,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(42)

fn main() -> i64:
    match get():
        case Ok(v):
            return v
        case Err(e):
            return -1
"#,
    42
);

backend_test!(
    jit_result_ok_unwrap_multiple_of_8,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(64)

fn main() -> i64:
    return get().unwrap()
"#,
    64
);

backend_test!(
    jit_result_ok_try_op_multiple_of_8,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(16)

fn caller() -> Result<i64, text>:
    let v: i64 = get()?
    return Ok(v)

fn main() -> i64:
    match caller():
        case Ok(v):
            return v
        case Err(e):
            return -1
"#,
    16
);

backend_test!(
    jit_result_ok_if_val_multiple_of_8,
    jit,
    r#"
fn get() -> Result<i64, text>:
    return Ok(48)

fn main() -> i64:
    if val Ok(v) = get():
        return v
    else:
        return -1
"#,
    48
);
