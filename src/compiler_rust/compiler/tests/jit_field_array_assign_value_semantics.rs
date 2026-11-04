//! JIT: `obj.buf = local_arr` must give the field its own copy (value
//! semantics), like `var c = arr` and like the interpreter. Before the fix the
//! field-store lowering stored the local's rt_array handle, so a write through
//! either binding showed up in the other.
//! Bug: doc/08_tracking/bug/seed_jit_class_field_array_assign_aliases_local_2026-11-04.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run_main(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn class_field_i64_array_assign_does_not_alias_local() {
    let src = "class Hold:
    buf: [i64]

fn main() -> i64:
    var a: [i64] = [1, 2]
    var h = Hold(buf: [])
    h.buf = a
    h.buf[0] = 9
    a[1] = 5
    a[0] * 1000 + h.buf[0] * 100 + a[1] * 10 + h.buf[1]
";
    assert_eq!(run_main(src), 1000 + 900 + 50 + 2);
}

#[test]
fn class_field_u8_array_assign_does_not_alias_local() {
    let src = "class Hold:
    buf: [u8]

fn main() -> i64:
    var a: [u8] = [1u8, 2u8]
    var h = Hold(buf: [])
    h.buf = a
    h.buf[0] = 9u8
    a[1] = 5u8
    (a[0] as i64) * 1000 + (h.buf[0] as i64) * 100 + (a[1] as i64) * 10 + (h.buf[1] as i64)
";
    assert_eq!(run_main(src), 1000 + 900 + 50 + 2);
}

#[test]
fn struct_field_array_assign_does_not_alias_local() {
    let src = "struct Hold:
    buf: [i64]

fn main() -> i64:
    var a: [i64] = [1, 2]
    var h = Hold(buf: [0, 0])
    h.buf = a
    h.buf[0] = 9
    a[0] * 10 + h.buf[0]
";
    assert_eq!(run_main(src), 19);
}
