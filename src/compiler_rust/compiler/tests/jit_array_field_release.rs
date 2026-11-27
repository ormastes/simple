//! JIT: `st.f = v` frees the replaced array buffer when `array_move.rs`
//! proves the field was its only holder, so a field overwritten in a loop no
//! longer leaks one buffer per iteration. Every sharing case must keep the
//! release OFF (checked on the MIR) and keep correct values.
//! Bug: doc/08_tracking/bug/seed_jit_array_copy_never_freed_2026-10-19.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use simple_runtime::value::heap::rt_heap_aux_live_bytes;

/// Returns (main's result, live aux bytes retained, rt_array_free sites in main).
fn run(src: &str) -> (i64, i64, usize) {
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let frees = mir_module
        .functions
        .iter()
        .find(|f| f.name == "main")
        .map(|f| format!("{:?}", f.blocks).matches("\"rt_array_free\"").count())
        .unwrap_or(0);
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let before = rt_heap_aux_live_bytes();
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    (v, rt_heap_aux_live_bytes() - before, frees)
}

const ST: &str = "class St:\n    buf: [i64]\n\n";

#[test]
fn field_overwrite_loop_is_flat() {
    let src = format!(
        "{ST}fn main() -> i64:
    var st = St(buf: [])
    var i = 0
    while i < 4096:
        var o: [i64] = []
        var k = 0
        while k < 64:
            o.push(i + k)
            k = k + 1
        st.buf = o
        i = i + 1
    st.buf[0] + st.buf.len()
"
    );
    let (v, live, frees) = run(&src);
    assert_eq!(v, 4095 + 64);
    assert!(frees >= 1, "field store must release the replaced buffer");
    // 4096 x 64 slots would be >= 2 MiB if every replaced buffer leaked.
    assert!(live < 64 * 1024, "replaced field buffers leaked: live={live}");
}

#[test]
fn place_copy_store_releases_and_keeps_source() {
    // `st.buf = a` copies (a live); the copy is freed on the next store, `a` is not.
    let src = format!(
        "{ST}fn main() -> i64:
    var st = St(buf: [0])
    var a: [i64] = [1, 2]
    st.buf = a
    st.buf[0] = 9
    st.buf = [5, 6, 7]
    a[0] * 100 + a.len() * 10 + st.buf.len()
"
    );
    assert_eq!(run(&src).0, 100 + 20 + 3);
}

#[test]
fn struct_literal_sharing_live_local_never_releases() {
    let src = format!(
        "{ST}fn main() -> i64:
    var o: [i64] = [1, 2]
    var st = St(buf: o)
    st.buf = [8]
    o.push(3)
    o.len() * 10 + st.buf[0]
"
    );
    let (v, _, frees) = run(&src);
    assert_eq!(v, 38);
    assert_eq!(frees, 0, "literal shares o's buffer: release must be off");
}

#[test]
fn moved_and_aliased_field_never_freed_under_holder() {
    // `x = st.buf` (plain assign) aliases the field: release must be off.
    let src = format!(
        "{ST}fn main() -> i64:
    var st = St(buf: [4, 5])
    var x: [i64] = []
    x = st.buf
    st.buf = [1]
    x[0] * 10 + x.len()
"
    );
    let (v, _, frees) = run(&src);
    assert_eq!(v, 42);
    assert_eq!(frees, 0);

    // `var t = st.buf` copies (st live): the original is freed, `t` survives.
    let src2 = format!(
        "{ST}fn main() -> i64:
    var st = St(buf: [4, 5])
    var t = st.buf
    st.buf = [1]
    t[0] * 100 + t[1] * 10 + st.buf[0]
"
    );
    assert_eq!(run(&src2).0, 451);
}

#[test]
fn nested_arrays_free_only_outer_buffer() {
    let src = "class G:
    rows: [[i64]]

fn main() -> i64:
    var r: [i64] = [1, 2]
    var g = G(rows: [])
    g.rows = [r]
    val row = g.rows[0]
    g.rows = [[7]]
    r.push(3)
    r.len() * 100 + row.len() * 10 + g.rows[0][0]
";
    assert_eq!(run(src).0, 327);
}

#[test]
fn closure_capture_never_releases() {
    let src = format!(
        "{ST}fn main() -> i64:
    var st = St(buf: [1, 2, 3])
    val f = \\: st.buf.len()
    st.buf = [9]
    f() * 10 + st.buf[0]
"
    );
    let (_, _, frees) = run(&src);
    assert_eq!(frees, 0, "captured struct must not release");
}

#[test]
fn field_passed_or_returned_never_freed_under_holder() {
    let src = format!(
        "{ST}fn keep(xs: [i64]) -> [i64]:
    xs

fn main() -> i64:
    var st = St(buf: [3, 4])
    val k = keep(st.buf)
    st.buf = [1]
    k[0] * 10 + k[1] + st.buf[0] * 100
"
    );
    let (v, _, frees) = run(&src);
    assert_eq!(v, 134);
    assert_eq!(frees, 0);

    let src2 = format!(
        "{ST}fn mk() -> [i64]:
    var st = St(buf: [1])
    st.buf = [6, 7]
    st.buf

fn main() -> i64:
    val r = mk()
    r[0] * 10 + r[1]
"
    );
    assert_eq!(run(&src2).0, 67);
}

#[test]
fn param_struct_never_releases() {
    let src = format!(
        "{ST}fn first(st: St) -> [i64]:
    st.buf

fn main() -> i64:
    var st = St(buf: [5])
    val held = first(st)
    st.buf = [2]
    held[0] * 10 + st.buf[0]
"
    );
    let (v, _, frees) = run(&src);
    assert_eq!(v, 52);
    assert_eq!(frees, 0, "struct passed to a call must not release");
}
