//! `&mut scalar_local` passed to an `extern fn` must reach the foreign side as
//! a real address and be written back into the local. The JIT used to pass
//! the VALUE (a null out pointer for `var h: i64 = 0`), so checked out-param
//! APIs rejected the call with status 1 and `main_gui` could not load its
//! window provider.
//! doc/08_tracking/bug/jit_refmut_extern_out_param_passes_value_not_address_2026-10-05.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

/// `spl_wffi_try_call_i64_out(0, [], 0, out)` zeroes a non-null out slot and
/// answers 2 (null function pointer); a null out slot answers 1.
#[test]
fn extern_out_slot_receives_address_and_is_written_back() {
    let src = r#"
extern fn spl_wffi_try_call_i64_out(fptr: i64, args: [i64], arg_count: i64, out_value: *mut i64) -> i64

fn main() -> i64:
    var probe: i64 = 99
    val status = spl_wffi_try_call_i64_out(0, [], 0, &mut probe)
    status * 1000 + probe
"#;
    assert_eq!(run(src), 2 * 1000 + 0);
}

/// A `bool` out slot: the foreign side writes ONE byte. This shape is
/// `_gui_free_bool` in gui_renderer.spl, whose first out-slot codegen
/// panicked ("declared type of variable doesn't match type of value") and
/// stub-fell-back the whole function.
#[test]
fn extern_bool_out_slot_compiles_and_writes_one_byte() {
    let src = r#"
extern fn spl_wffi_call_bool1_checked(fptr: i64, arg0: i64, out_value: *mut bool) -> i64

fn probe(seed: bool) -> i64:
    var released = seed
    val status = spl_wffi_call_bool1_checked(0, 0, &mut released)
    if released:
        return status * 10 + 1
    status * 10

fn main() -> i64:
    probe(true) * 1000 + probe(false)
"#;
    // fptr 0: the out slot is written `false`, then status 2 (null function).
    assert_eq!(run(src), 20 * 1000 + 20);
}

/// Generalization: the slot round-trips across a loop and branch, and a
/// second out-param call in the same function writes its own local.
#[test]
fn extern_out_slots_in_loop_write_back_each_local() {
    let src = r#"
extern fn spl_wffi_try_call_i64_out(fptr: i64, args: [i64], arg_count: i64, out_value: *mut i64) -> i64

fn main() -> i64:
    var a: i64 = 7
    var b: i64 = 8
    var total: i64 = 0
    var i = 0
    while i < 3:
        if i == 1:
            total = total + spl_wffi_try_call_i64_out(0, [], 0, &mut a)
        else:
            total = total + spl_wffi_try_call_i64_out(0, [], 0, &mut b)
        i = i + 1
    total * 100 + a * 10 + b
"#;
    assert_eq!(run(src), 6 * 100 + 0 * 10 + 0);
}
