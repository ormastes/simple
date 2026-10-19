//! Unsigned integers keep unsigned semantics on every seed engine.
//!
//! A `u64` value >= 2^63 is carried as an `i64` bit pattern. Comparisons,
//! division, remainder, and right shifts on it must still be unsigned wherever
//! the static type is unsigned. The interpreter used to drop the annotation on
//! module-level `val`/`const` bindings (so an imported `VMM_KERNEL_SPACE_START`
//! compared as a negative number) and on `-> u64` returns; the JIT typed every
//! integer literal as `i64`, so `0xFFFF_FFFF_FFFF_FFF8u64 > 5u64` was false.
//! The case number returned by `main` names the first row that differs.
//! Bug: doc/08_tracking/bug/seed_u64_signed_compare_and_u8_data_ptr_2026-10-19.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

/// Same-module rows: both engines must return 0.
const SOURCE: &str = r#"
val KSTART: u64 = 0xFFFF800000000000
const CTOP: u64 = 0x8000000000000000

fn kstart_fn() -> u64:
    0xFFFF800000000000

fn main() -> i64:
    val ptr: u64 = 0x7FF0
    val three: u64 = 3
    if not (ptr < KSTART): return 1
    if not (ptr < CTOP): return 2
    if not (ptr < kstart_fn()): return 3
    if not (0xFFFFFFFFFFFFFFF8u64 > 5u64): return 4
    if not (5u64 < 0xFFFFFFFFFFFFFFF8u64): return 5
    if 0x8000000000000000u64 / 2u64 != 4611686018427387904u64: return 6
    if 0xFFFFFFFFFFFFFFFFu64 >> 60u64 != 15u64: return 7
    if 0xFFFFFFFFFFFFFFFFu64 % 10u64 != 5u64: return 8
    if 0xFFFFFFFFFFFFFFFFu64 / three != 6148914691236517205u64: return 9
    if CTOP / 2u64 != 4611686018427387904u64: return 10
    var w: u32 = 0
    w = w - 1u32
    if not (w > 1u32): return 11
    if w / 2u32 != 2147483647u32: return 12
    if w >> 31u32 != 1u32: return 13
    val signed_neg: i64 = -8
    if not (signed_neg < 5): return 14
    if signed_neg / 2 != -4: return 15
    if signed_neg >> 1 != -4: return 16
    return 0
"#;

fn run_interpreter(source: &str) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{source}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("source must run in interpreter")
}

fn run_jit(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn unsigned_compare_div_shift_match_on_interpreter_and_jit() {
    let interpreted = run_interpreter(SOURCE);
    assert_eq!(interpreted, 0, "interpreter failed at case {interpreted}");
    let native = run_jit(SOURCE);
    assert_eq!(native, 0, "JIT failed at case {native}");
}

/// Imported typed module values: the interpreter's module evaluator path.
#[test]
fn imported_typed_u64_module_values_stay_unsigned_in_interpreter() {
    let dir = tempdir().unwrap();
    fs::write(
        dir.path().join("consts.spl"),
        "val KSTART: u64 = 0xFFFF800000000000\n\
         val UMAX: u64 = 0xFFFFFFFFFFFFFFFF\n\
         const CTOP: u64 = 0x8000000000000000\n\
         val U32MAX: u32 = 0xFFFFFFFF\n",
    )
    .unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "use consts.{KSTART, UMAX, CTOP, U32MAX}\n\
         \n\
         fn main() -> i32:\n\
         \x20   val ptr: u64 = 0x7FF0\n\
         \x20   if not (ptr < KSTART): return 1\n\
         \x20   if not (ptr < UMAX): return 2\n\
         \x20   if not (CTOP > ptr): return 3\n\
         \x20   if UMAX >> 60u64 != 15u64: return 4\n\
         \x20   if UMAX / 2u64 != 9223372036854775807u64: return 5\n\
         \x20   if not (U32MAX > 1u32): return 6\n\
         \x20   return 0\n",
    )
    .unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .expect("module graph must load");
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    assert_eq!(result.expect("program must run"), 0);
}

/// `rt_array_data_ptr` on live `[u8]` arrays: never 0 for a non-empty array.
/// Theme-notification shape: build with `var out: [u8] = []` + `out = out.push(..)`,
/// return through a helper and a `Result`, then read the bytes back through the
/// pointer.
const DATA_PTR_SOURCE: &str = r#"
extern fn rt_array_data_ptr(array: [u8]) -> i64
extern fn rt_ptr_read_u8(ptr: i64, offset: i64) -> i64

fn push_le16(out: [u8], v: u32) -> [u8]:
    var o = out
    o = o.push((v & 0xFF).to_u8())
    o = o.push(((v >> 8) & 0xFF).to_u8())
    o

fn encode() -> Result<[u8], text>:
    var out: [u8] = []
    out = push_le16(out, 0x0201u32)
    out = out.push(3u8)
    Ok(out)

fn main() -> i64:
    var payload: [u8] = []
    match encode():
        Ok(bytes): payload = bytes
        Err(_): return 1
    val ptr = rt_array_data_ptr(payload)
    if ptr == 0: return 2
    if rt_ptr_read_u8(ptr, 0) != 1: return 3
    if rt_ptr_read_u8(ptr, 2) != 3: return 4
    var pushed: [u8] = []
    pushed.push(7u8)
    val pushed_ptr = rt_array_data_ptr(pushed)
    if pushed_ptr == 0: return 5
    if rt_ptr_read_u8(pushed_ptr, 0) != 7: return 6
    val literal: [u8] = [9u8, 8u8]
    val literal_ptr = rt_array_data_ptr(literal)
    if literal_ptr == 0: return 7
    if rt_ptr_read_u8(literal_ptr, 1) != 8: return 8
    val empty: [u8] = []
    if rt_array_data_ptr(empty) == 0: return 9
    return 0
"#;

#[test]
fn u8_data_ptr_is_live_on_interpreter_and_jit() {
    let interpreted = run_interpreter(DATA_PTR_SOURCE);
    assert_eq!(interpreted, 0, "interpreter failed at case {interpreted}");
    let native = run_jit(DATA_PTR_SOURCE);
    assert_eq!(native, 0, "JIT failed at case {native}");
}

/// A non-empty boxed `[u8]` (untyped struct-field `[]` + push) has no
/// contiguous storage in the interpreter: it must fail loudly, not answer 0.
#[test]
fn boxed_u8_array_data_ptr_fails_loudly_in_interpreter() {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = r#"
extern fn rt_array_data_ptr(array: [u8]) -> i64

struct Holder:
    bytes: [u8]

fn main() -> i64:
    var slot = Holder(bytes: []).bytes
    slot.push(5u8)
    if rt_array_data_ptr(slot) == 0: return 1
    return 0

main = main()
"#;
    let module = Parser::new(source).parse().expect("source must parse");
    let error = interpreter::evaluate_module(&module.items).expect_err("boxed [u8] data_ptr must not answer");
    assert!(
        format!("{error:?}").contains("non-contiguous"),
        "unexpected error: {error:?}"
    );
}
