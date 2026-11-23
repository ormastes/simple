//! JIT: the "take" idiom on an array field,
//!
//! ```text
//! var surface = self.buf
//! self.buf = []
//! surface.write_span(...)
//! self.buf = surface
//! ```
//!
//! must move the buffer out and back, not copy it twice. The `Let` from a
//! place emitted `rt_array_copy` and the store back emitted a second one, and
//! the JIT never frees either, so each call leaked two whole buffers. The
//! engine2d software backend uses this idiom once per span; at device scale 4
//! (3600x3040 surface) every web catalog page was OOM-killed at 8 GB.
//! Bug: doc/08_tracking/bug/jit_take_field_array_idiom_copies_and_leaks_surface_2026-11-23.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use simple_runtime::value::heap::rt_heap_aux_live_bytes;

/// Returns (main's result, live aux bytes retained, rt_array_copy sites in `fn_name`).
fn run(src: &str, fn_name: &str) -> (i64, i64, usize) {
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let copies = mir_module
        .functions
        .iter()
        .find(|f| f.name.ends_with(fn_name))
        .map(|f| format!("{:?}", f.blocks).matches("\"rt_array_copy\"").count())
        .expect("function must exist in MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let before = rt_heap_aux_live_bytes();
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    (v, rt_heap_aux_live_bytes() - before, copies)
}

const BACK: &str = "class Back:
    buf: [i64]

    me put(src: [i64], off: i64):
        var surface = self.buf
        self.buf = []
        surface.write_span(src, off, 0, src.len())
        self.buf = surface

";

#[test]
fn take_idiom_moves_without_copy_and_is_flat() {
    let src = format!(
        "{BACK}fn main() -> i64:
    var b = Back(buf: [0; 4096])
    val src: [i64] = [7, 8, 9]
    var i = 0
    while i < 2000:
        b.put(src, i)
        i = i + 1
    b.buf[0] * 1000 + b.buf[1999 + 2] * 10 + b.buf.len() - 4096
"
    );
    let (v, live, copies) = run(&src, ".put");
    assert_eq!(v, 7 * 1000 + 9 * 10);
    assert_eq!(copies, 0, "take idiom must not copy the field buffer");
    // 2000 calls x 2 copies x 4096 slots x 8 B would retain ~131 MB.
    assert!(live < 4 * 1024 * 1024, "take idiom leaked buffers: live={live}");
}

#[test]
fn take_idiom_result_matches_direct_write() {
    let src = format!(
        "{BACK}fn main() -> i64:
    var b = Back(buf: [1, 2, 3, 4, 5])
    b.put([40, 50], 3)
    b.put([9], 0)
    var s = 0
    for x in b.buf:
        s = s * 100 + x
    s
"
    );
    // 9 2 3 40 50
    assert_eq!(run(&src, ".put").0, 902034050);
}

#[test]
fn let_from_field_without_take_still_copies() {
    // No `self.buf = []` right after the `Let`: the field still holds the
    // buffer, so the local must get a private copy (value semantics).
    let src = "class Back:
    buf: [i64]

    me peek() -> i64:
        var c = self.buf
        c[0] = 99
        self.buf[0]

fn main() -> i64:
    var b = Back(buf: [5, 6])
    b.peek()
";
    let (v, _, copies) = run(src, ".peek");
    assert_eq!(v, 5);
    assert!(copies >= 1, "a non-take Let from a field must keep its copy");
}

#[test]
fn conditional_assign_take_store_back_does_not_copy() {
    // `SoftwareBackend.draw_image_blend` shape: the take is an `Assign`
    // inside an `if`, the store back is guarded by the same flag.
    let src = "class Back:
    buf: [i64]

    me blit(src: [i64], masked: bool):
        var b: [i64] = []
        if not masked:
            b = self.buf
            self.buf = []
        var i = 0
        while i < src.len():
            if not masked:
                b[i] = src[i] + b[i]
            i = i + 1
        if not masked:
            self.buf = b

fn main() -> i64:
    var bk = Back(buf: [0; 4096])
    val src: [i64] = [1, 2, 3]
    var n = 0
    while n < 2000:
        bk.blit(src, false)
        n = n + 1
    bk.blit(src, true)
    bk.buf[0] * 10000 + bk.buf[2] + bk.buf.len() - 4096
";
    let (v, live, copies) = run(src, ".blit");
    assert_eq!(v, 2000 * 10000 + 6000);
    assert_eq!(copies, 0, "conditional take must hand the buffer back without a copy");
    assert!(live < 4 * 1024 * 1024, "conditional take leaked buffers: live={live}");
}

#[test]
fn take_that_escapes_before_store_back_keeps_copy() {
    // `x` is shared with another field before the store back: the store must
    // keep its private copy, or both fields would hold one buffer.
    let src = "class Two:
    a: [i64]
    b: [i64]

    me swap_in():
        var x = self.a
        self.a = []
        self.b = x
        x[0] = 7
        self.a = x

fn main() -> i64:
    var t = Two(a: [1, 2], b: [])
    t.swap_in()
    t.a[0] * 10 + t.b[0]
";
    let (v, _, copies) = run(src, ".swap_in");
    assert_eq!(v, 7 * 10 + 1);
    assert!(copies >= 1, "an escaping take must keep the store-back copy");
}

#[test]
fn take_reassigned_from_parameter_keeps_store_copy() {
    // `x` later holds the caller's array: storing it must copy, or the field
    // and the caller's local would share one buffer.
    let src = "class Back:
    buf: [i64]

    me swap(other: [i64]):
        var x = self.buf
        self.buf = []
        x = other
        self.buf = x

fn main() -> i64:
    var b = Back(buf: [1])
    var o: [i64] = [5, 6]
    b.swap(o)
    b.buf[0] = 9
    o[0] * 10 + b.buf[0]
";
    let (v, _, copies) = run(src, ".swap");
    assert_eq!(v, 5 * 10 + 9);
    assert!(copies >= 1, "a take later re-bound to a parameter must keep the store copy");
}

#[test]
fn take_store_back_inside_loop_keeps_copy() {
    let src = "class Back:
    buf: [i64]
    keep: [i64]

    me twice():
        var x = self.buf
        self.buf = []
        var i = 0
        while i < 2:
            x[0] = x[0] + 1
            self.keep = x
            i = i + 1

fn main() -> i64:
    var b = Back(buf: [0], keep: [])
    b.twice()
    b.keep[0]
";
    let (v, _, copies) = run(src, ".twice");
    assert_eq!(v, 2);
    assert!(copies >= 1, "a store back inside a loop must keep its copy");
}
