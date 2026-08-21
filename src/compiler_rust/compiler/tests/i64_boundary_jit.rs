//! Cranelift JIT: i64 values at and past the tagged-immediate boundary, and
//! the signed-division overflow case.
//!
//! Two defects, both found by the multi-engine differential harness
//! (`scripts/check/check_engine_differential.spl`, fixture
//! `test/fixtures/engine_differential/i64_boundary_values.spl`):
//!
//! 1. `RuntimeValue::from_int` stored `i << 3` with NO range check, so every
//!    value needing 61+ bits was silently truncated and sign-extended back on
//!    the way out of a container: `2^60` came back negative, `2^62` came back
//!    `0`, `i64::MAX` came back `-1`. The interpreter was correct throughout.
//!    doc/08_tracking/bug/int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md
//!
//! 2. `INT64_MIN / -1` lowered to a bare `sdiv`. x86 `idiv` raises #DE for the
//!    one quotient it cannot represent, so the process died with SIGFPE while
//!    the interpreter wrapped to `INT64_MIN`. Wrapping is this language's
//!    integer rule -- `0 - INT64_MIN` already wrapped on BOTH engines -- so the
//!    JIT was the wrong engine.
//!
//! `main` returns 0 on success and a distinct non-zero case number otherwise,
//! so a failure names the exact row rather than just "not equal".

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

/// Scalars and container elements, on both sides of the 2^60 inline boundary.
/// The container rows are the ones that were corrupt: a scalar never enters the
/// tagged representation at all, which is exactly why a scalar-only probe
/// reported this defect as already fixed.
#[test]
fn wide_i64_values_survive_boxing_into_a_container() {
    let source = r#"
fn identity(v: i64) -> i64:
    v

fn main() -> i64:
    # Below the boundary: unchanged, and the non-vacuity control.
    if identity(42) != 42: return 1
    if identity(576460752303423488) != 576460752303423488: return 2
    if [42][0] != 42: return 3
    if [576460752303423488][0] != 576460752303423488: return 4

    # -2^60 is the LAST value that fits inline; 2^60 is the first that does not.
    # The range is asymmetric, exactly as two's complement requires.
    if [-1152921504606846976][0] != -1152921504606846976: return 5
    if [1152921504606846975][0] != 1152921504606846975: return 6
    if [1152921504606846976][0] != 1152921504606846976: return 7
    if [-1152921504606846977][0] != -1152921504606846977: return 8

    # The values named in the bug report. Pre-fix: 2^60 came back negative,
    # 2^62 came back 0, i64::MAX came back -1.
    if [4611686018427387904][0] != 4611686018427387904: return 9
    if [9223372036854775807][0] != 9223372036854775807: return 10
    if [-9223372036854775807][0] != -9223372036854775807: return 11
    if [-9223372036854775808][0] != -9223372036854775808: return 12

    # Multi-element, so a wide box cannot be confused with the whole array, and
    # a wide element next to a small one keeps both.
    val mixed = [1152921504606846976, 42, 9223372036854775807]
    if mixed[0] != 1152921504606846976: return 13
    if mixed[1] != 42: return 14
    if mixed[2] != 9223372036854775807: return 15
    if mixed.len() != 3: return 16

    # Two boxes of the same wide value must compare equal BY VALUE. If they
    # compared by pointer this would fail even though both round-trip.
    if [9223372036854775807][0] != [9223372036854775807][0]: return 17
    return 0
"#;
    assert_eq!(run(source), 0, "wide-i64 boxing probe failed at case");
}

/// Signed division and remainder at the one overflowing input. Pre-fix the
/// process died with SIGFPE here, so this test could not even report a failure
/// -- it took the whole test binary down.
#[test]
fn int64_min_divided_by_negative_one_wraps_instead_of_faulting() {
    let source = r#"
fn main() -> i64:
    val imin = -9223372036854775808
    # The overflowing quotient: wraps to INT64_MIN, matching the interpreter.
    if imin / -1 != -9223372036854775808: return 1
    # x % -1 is 0 for every x, including the one x86 faults on.
    if imin % -1 != 0: return 2
    if 42 % -1 != 0: return 3
    if -42 % -1 != 0: return 4
    # abs(INT64_MIN) wraps too, and already did before the fix -- the control
    # that establishes wrapping (not trapping) is the rule being matched.
    if 0 - imin != -9223372036854775808: return 5

    # Ordinary signed division must be untouched by the guard. Truncation is
    # toward zero and the remainder takes the sign of the DIVIDEND.
    if -100 / 7 != -14: return 6
    if -100 % 7 != -2: return 7
    if 100 / -7 != -14: return 8
    if 100 % -7 != 2: return 9
    if -100 / -7 != 14: return 10
    if 100 / 7 != 14: return 11
    # Divisor -1 on ordinary values still negates.
    if 42 / -1 != -42: return 12
    if -42 / -1 != 42: return 13
    if 0 / -1 != 0: return 14
    return 0
"#;
    assert_eq!(run(source), 0, "signed div/rem probe failed at case");
}

/// Shift counts at and past the word width. These already AGREED between the
/// engines (both mask the count mod 64); the test exists so a future change to
/// the shift lowering cannot silently split them.
#[test]
fn shift_counts_at_and_past_the_word_width_agree_with_the_interpreter() {
    let source = r#"
fn main() -> i64:
    if 1 << 64 != 1: return 1
    if 1 << 65 != 2: return 2
    if 9223372036854775807 >> 64 != 9223372036854775807: return 3
    if 1 << 63 != -9223372036854775808: return 4
    if 1 << 60 != 1152921504606846976: return 5
    if -9223372036854775808 >> 63 != -1: return 6
    return 0
"#;
    assert_eq!(run(source), 0, "shift-count probe failed at case");
}
