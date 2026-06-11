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
