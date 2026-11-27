//! Erased (`Any`) values crossing a typed boundary on the JIT:
//!
//! - an erased int passed into a typed `i64` parameter must arrive untagged
//!   (seed_jit_erased_int_not_unboxed_at_typed_call_2026-11-04);
//! - a native scalar pushed onto an erased array receiver must be stored as a
//!   tagged RuntimeValue, so it reads back unchanged
//!   (seed_jit_untyped_to_u8_push_double_untag_2026-10-18).

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    // Untyped params need the `run` lane's lenient type mode.
    let hir_module = hir::lower_with_context_lenient(&ast, std::path::Path::new("erased_scalar_boundary.spl"))
        .expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn erased_ints_reach_typed_i64_params_untagged() {
    let src = r#"fn modq(x: i64) -> i64:
    x % 3329

fn pair() -> [Any]:
    return [1000, 589]

fn via_list(xs) -> i64:
    val fj = xs.get(0)
    val t = xs.get(1)
    modq(fj + t)

fn main() -> i64:
    val ci = pair()
    if modq(ci[0]) != 1000: return 1
    if modq(ci[0] + ci[1]) != 1589: return 2
    if via_list([1000, 589]) != 1589: return 3
    return 0
"#;
    assert_eq!(run(src), 0);
}

#[test]
fn scalar_pushed_onto_erased_array_reads_back_unchanged() {
    let src = r#"fn push_u8(bs, v: i64) -> [Any]:
    var bytes = bs[0]
    bytes.push(v.to_u8())
    return [bytes]

fn push_i64(bs, v: i64) -> [Any]:
    var words = bs[0]
    words.push(v)
    return [words]

fn main() -> i64:
    var e1: [u8] = []
    val r1 = push_u8([e1], 99)
    val b: [u8] = r1[0]
    if b.len() != 1: return 1
    val got_b: i64 = b[0]
    if got_b != 99: return 2
    var e2: [i64] = []
    val r2 = push_i64([e2], 99)
    val w: [i64] = r2[0]
    val got_w: i64 = w[0]
    if got_w != 99: return 3
    return 0
"#;
    assert_eq!(run(src), 0);
}

/// `(x & 255).to_u8()` with an untyped `x` (gzip footer shape): the masked
/// value is computed raw then boxed, and the cast must not narrow the tag word.
#[test]
fn cast_of_arithmetic_on_untyped_param_is_not_tagged() {
    let src = r#"fn low_byte(x) -> i64:
    var out: [u8] = []
    out.push((x & 255).to_u8())
    val b: i64 = out[0]
    b

fn main() -> i64:
    if low_byte(0x12345678) != 120: return 1
    if low_byte(0x56) != 86: return 2
    return 0
"#;
    assert_eq!(run(src), 0);
}
