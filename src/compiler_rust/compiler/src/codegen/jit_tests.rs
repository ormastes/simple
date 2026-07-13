//! Tests for JIT compilation

use super::*;
use crate::hir;
use crate::mir::lower_to_mir;
use simple_parser::Parser;

fn jit_compile(source: &str) -> JitResult<JitCompiler> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    let mir_module = lower_to_mir(&hir_module).expect("mir lower failed");

    let mut jit = JitCompiler::new()?;
    jit.compile_module(&mir_module)?;
    Ok(jit)
}

#[test]
fn test_jit_simple_return() {
    let jit = jit_compile("fn answer() -> i64:\n    return 42\n").unwrap();
    let result = unsafe { jit.call_i64_void("answer").unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_add() {
    let jit = jit_compile("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();
    let result = unsafe { jit.call_i64_i64_i64("add", 10, 32).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_subtract() {
    let jit = jit_compile("fn sub(a: i64, b: i64) -> i64:\n    return a - b\n").unwrap();
    let result = unsafe { jit.call_i64_i64_i64("sub", 50, 8).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_multiply() {
    let jit = jit_compile("fn mul(a: i64, b: i64) -> i64:\n    return a * b\n").unwrap();
    let result = unsafe { jit.call_i64_i64_i64("mul", 6, 7).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_negate() {
    let jit = jit_compile("fn neg(x: i64) -> i64:\n    return -x\n").unwrap();
    let result = unsafe { jit.call_i64_i64("neg", -42).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_conditional() {
    let jit =
        jit_compile("fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n")
            .unwrap();

    let result1 = unsafe { jit.call_i64_i64_i64("max", 42, 10).unwrap() };
    assert_eq!(result1, 42);

    let result2 = unsafe { jit.call_i64_i64_i64("max", 10, 42).unwrap() };
    assert_eq!(result2, 42);
}

#[test]
fn test_jit_recursive_factorial() {
    let jit = jit_compile(
        r#"fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)
"#,
    )
    .unwrap();

    let result = unsafe { jit.call_i64_i64("factorial", 5).unwrap() };
    assert_eq!(result, 120);
}

#[test]
fn test_jit_println_capture() {
    use simple_runtime::value::{rt_capture_stdout_start, rt_capture_stdout_stop};

    // Use static provider explicitly to avoid TLS issues with dynamic loading
    let mut jit = JitCompiler::new_static().unwrap();

    let mut parser = simple_parser::Parser::new(
        r#"fn greet() -> i64:
    println("hello jit")
    return 0
"#,
    );
    let ast = parser.parse().expect("parse failed");
    let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
    let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
    jit.compile_module(&mir_module).unwrap();

    // Start capture
    rt_capture_stdout_start();

    // Call the JIT function
    let result = unsafe { jit.call_i64_void("greet").unwrap() };

    // Stop capture and get result
    let captured = rt_capture_stdout_stop();

    assert_eq!(result, 0);
    assert_eq!(
        captured, "hello jit\n",
        "JIT println should be captured, got: '{}'",
        captured
    );
}

#[test]
fn test_jit_module_init_writes_heap_initialized_val_global() {
    let source = r#"
val DRAW_IR_BACKEND_CPU = "cpu"

fn fb_put(mut fb: [u32], fbw: i64, fbh: i64, x: i64, y: i64, color: u32):
    if x < 0 or y < 0 or x >= fbw or y >= fbh:
        return
    fb[y * fbw + x] = color

fn main() -> i64:
    return 1
"#;
    let jit = jit_compile(source).unwrap();
    let result = unsafe { jit.call_i64_void("main").unwrap() };
    assert_eq!(result, 1);
}

#[test]
fn test_jit_module_init_all_zero_array_compact_fill_loop() {
    // All-zero module-level array initializers ([0; N]) are emitted as a
    // compact runtime fill loop instead of N unrolled push calls. The array
    // must still be a real length-N zero-filled array handle (NOT a null/.bss
    // zero handle), and nonzero initializers must be unaffected.
    let source = r#"
var big: [i64; 100000] = [0; 100000]
var ones: [i64; 8] = [1; 8]

fn big_len() -> i64:
    return big.len()

fn big_at_123() -> i64:
    return big[123]

fn big_at_last() -> i64:
    return big[99999]

fn ones_at_7() -> i64:
    return ones[7]
"#;
    let jit = jit_compile(source).unwrap();
    let len = unsafe { jit.call_i64_void("big_len").unwrap() };
    assert_eq!(len, 100000, "all-zero [0; N] global must still have length N");
    let elem = unsafe { jit.call_i64_void("big_at_123").unwrap() };
    assert_eq!(elem, 0, "all-zero [0; N] global elements must read 0");
    let last = unsafe { jit.call_i64_void("big_at_last").unwrap() };
    assert_eq!(last, 0, "all-zero [0; N] global last element must read 0");
    let one = unsafe { jit.call_i64_void("ones_at_7").unwrap() };
    assert_eq!(one, 1, "nonzero repeat initializer must be unaffected");
}

#[test]
fn test_jit_module_init_boolean_array_preserves_false_and_true() {
    let source = r#"
var flags: [bool] = [false, true]
var disabled: bool = false

fn flags_len() -> i64:
    flags.len()

fn flags_score() -> i64:
    if disabled:
        return 100
    if flags[0]:
        return 10
    if flags[1]:
        return 1
    0
"#;
    let jit = jit_compile(source).unwrap();
    let len = unsafe { jit.call_i64_void("flags_len").unwrap() };
    assert_eq!(len, 2);
    let score = unsafe { jit.call_i64_void("flags_score").unwrap() };
    assert_eq!(score, 1);
}

#[test]
fn test_jit_i32_return_controls_loop_condition() {
    let source = r#"
fn as_i32(v: i64) -> i32:
    return v.to_i32()

fn should_skip() -> i64:
    val sample_count = as_i32(0)
    var i: i64 = 0
    while i < sample_count:
        return 99
    return 0
"#;
    let jit = jit_compile(source).unwrap();
    let result = unsafe { jit.call_i64_void("should_skip").unwrap() };
    assert_eq!(result, 0);
}

#[test]
fn test_jit_text_to_i32_parses_string_before_narrowing() {
    let source = r#"
fn parsed_zero_skips_loop() -> i64:
    val sample_count = "0".to_i32()
    var i: i64 = 0
    while i < sample_count:
        return 99
    return sample_count.to_i64()
"#;
    let jit = jit_compile(source).unwrap();
    let result = unsafe { jit.call_i64_void("parsed_zero_skips_loop").unwrap() };
    assert_eq!(result, 0);
}

#[test]
fn test_jit_i32_struct_fields_do_not_retain_stale_upper_bits() {
    let source = r#"
struct CountSample:
    warmup_count: i32
    sample_count: i32

fn as_i32(v: i64) -> i32:
    return v.to_i32()

fn read_sample_count() -> i64:
    val sample = CountSample(warmup_count: as_i32(0), sample_count: as_i32(0))
    if sample.sample_count == 0:
        return 0
    return 99
"#;
    let jit = jit_compile(source).unwrap();
    let result = unsafe { jit.call_i64_void("read_sample_count").unwrap() };
    assert_eq!(result, 0);
}

#[test]
fn test_jit_static_provider_resolves_generic_rt_len() {
    simple_runtime::register_static_runtime_symbols();
    let provider = static_provider();
    assert!(
        provider.get_symbol("rt_len").is_some(),
        "rt_len must be registered so dynamic len() lowering does not NULL-jump in JIT"
    );
    assert!(
        provider.get_symbol("rt_time_now_unix_micros").is_some(),
        "rt_time_now_unix_micros must be registered so timing helpers do not NULL-jump in JIT"
    );
}

// Regression: an f64 function-call result was corrupted at the call boundary.
// The uniform i64 return ABI carries an f64 return as raw bits, but the return
// terminator value-converted it (fcvt_to_sint: `return 21.5` -> integer 21), and
// MirInst::Call results were left unstamped so f64 consumers treated the i64 bits
// as an integer. Result: an f64 call result bound to a local, fed into a binop,
// or passed as an argument came out as ~0.0 / garbage. Fixed in
// codegen/instr/body.rs (Return bitcast + build_vreg_types f64 stamping).
#[test]
fn test_jit_f64_call_result_value() {
    let source = r#"
fn half() -> f64:
    return 21.5
fn add(a: f64, b: f64) -> f64:
    return a + b
fn consume(v: f64) -> i64:
    if v > 5.0:
        return 1
    return 0
fn main() -> i64:
    var score = 0
    val x = half()
    if x > 5.0:
        score = score + 1
    if half() + half() > 42.0:
        score = score + 1
    if add(1.5, 2.25) > 3.0:
        score = score + 1
    if consume(half()) > 0:
        score = score + 1
    return score
"#;
    let jit = jit_compile(source).unwrap();
    let result = unsafe { jit.call_i64_void("main").unwrap() };
    assert_eq!(
        result, 4,
        "all 4 f64 call-result cases (bound local, binop of two calls, binop on \
         params, call result as fn arg) must be correct; got score {}",
        result
    );
}

// Regression: an f64 call result passed to print() showed 0.0 because the result
// carried mangled bits and was boxed as an integer. With the fix print(half())
// formats the real value.
#[test]
fn test_jit_f64_call_result_print() {
    use simple_runtime::value::{rt_capture_stdout_start, rt_capture_stdout_stop};

    let mut jit = JitCompiler::new_static().unwrap();
    let mut parser = simple_parser::Parser::new(
        "fn half() -> f64:\n    return 21.5\nfn main() -> i64:\n    print(half())\n    return 0\n",
    );
    let ast = parser.parse().expect("parse failed");
    let hir_module = crate::hir::lower(&ast).expect("hir lower failed");
    let mir_module = crate::mir::lower_to_mir(&hir_module).expect("mir lower failed");
    jit.compile_module(&mir_module).unwrap();

    rt_capture_stdout_start();
    let result = unsafe { jit.call_i64_void("main").unwrap() };
    let captured = rt_capture_stdout_stop();

    assert_eq!(result, 0);
    assert_eq!(
        captured.trim(),
        "21.5",
        "print() of an f64 call result must format the value, got: '{}'",
        captured
    );
}
