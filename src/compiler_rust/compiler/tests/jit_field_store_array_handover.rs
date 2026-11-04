//! JIT: `st.buf = o` from a `var` array local that is dead after the store
//! must hand the buffer over, not `rt_array_copy` it. The JIT lane never frees
//! the copy, so the copy-on-every-field-store rule (PR #6627) retained one
//! extra buffer per loop iteration.
//! Bug: doc/08_tracking/bug/seed_jit_field_store_array_copy_never_freed_2026-11-04.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use simple_runtime::value::heap::rt_heap_aux_live_bytes;

fn compile(source: &str) -> JitCompiler {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    jit
}

fn run_bytes(src: &str) -> (i64, i64) {
    let jit = compile(src);
    let before = rt_heap_aux_live_bytes();
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    (v, rt_heap_aux_live_bytes() - before)
}

/// `TAIL` is spliced after the store: empty = `o` dead (hand-over), `o.len()`
/// read = `o` live (must copy).
fn loop_src(tail: &str) -> String {
    format!(
        "class St:
    buf: [i64]

fn main() -> i64:
    var st = St(buf: [])
    var extra = 0
    var i = 0
    while i < 4096:
        var o: [i64] = []
        var k = 0
        while k < 64:
            o.push(i + k)
            k = k + 1
        st.buf = o
        {tail}
        i = i + 1
    st.buf[0] + extra
"
    )
}

#[test]
fn dead_local_field_store_does_not_retain_a_copy_per_iteration() {
    let (v_move, moved) = run_bytes(&loop_src("extra = 0"));
    let (v_copy, copied) = run_bytes(&loop_src("extra = o.len() - 64"));
    assert_eq!(v_move, 4095);
    assert_eq!(v_copy, 4095);
    // The live twin keeps one 64-slot copy per iteration on top of `o`; the
    // hand-over twin must not. Measured: moved ~= copied * 0.6 after the fix,
    // moved == copied before it.
    assert!(
        moved * 10 < copied * 8,
        "dead-local field store retained per-iteration copies: moved={moved} copied={copied}"
    );
}

#[test]
fn handed_over_field_store_keeps_value_semantics() {
    // `a` is live after the store: must copy. `b` is dead: handed over, and
    // the field still owns a correct buffer.
    let src = "class Hold:
    buf: [i64]

fn main() -> i64:
    var h = Hold(buf: [])
    var a: [i64] = [1, 2]
    h.buf = a
    h.buf[0] = 9
    val a0 = a[0]
    var b: [i64] = [3, 4]
    h.buf = b
    h.buf[1] = 7
    a0 * 1000 + h.buf[0] * 10 + h.buf[1]
";
    let (v, _) = run_bytes(src);
    assert_eq!(v, 1000 + 30 + 7);
}

#[test]
fn field_store_in_loop_from_outer_local_still_copies() {
    // `o` outlives each store (declared outside the loop), so every store must
    // snapshot it: later pushes to `o` must not reach `st.buf`.
    let src = "class St:
    buf: [i64]

fn main() -> i64:
    var st = St(buf: [])
    var o: [i64] = []
    var i = 0
    while i < 3:
        o.push(i)
        st.buf = o
        i = i + 1
    o.push(99)
    st.buf.len() * 10 + o.len()
";
    let (v, _) = run_bytes(src);
    assert_eq!(v, 34);
}
