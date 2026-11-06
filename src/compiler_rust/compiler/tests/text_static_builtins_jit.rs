//! Cranelift JIT: builtin text statics `text.from_char_code(code)` and
//! `text.from_bytes(bytes)` lower to the canonical runtime ABI
//! (`rt_char_from_code` / `rt_bytes_to_text`), as the LLVM backend already did
//! (`codegen/llvm/functions/calls.rs`). Cranelift instead emitted a call to the
//! sanitized dotted name `text_dot_from_char_code`. That legacy symbol is
//! deliberately absent from the static provider manifest, so the call
//! either panicked at link time (2026-09-04) or, on the current seed, jumped
//! through an unusable import and died with SIGSEGV.
//! doc/08_tracking/bug/seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    simple_runtime::register_static_runtime_symbols();
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn text_static_builtins_route_to_runtime_abi() {
    let source = r#"
fn main() -> i64:
    val s = text.from_char_code(65)
    if s != "A":
        return 1
    val e = text.from_char_code(233)
    if e.len() != 2 or e.char_code_at(0) != 233:
        return 2
    val b = text.from_bytes([104u8, 105u8])
    if b != "hi":
        return 3
    0
"#;
    assert_eq!(run(source), 0);
}

/// Exact shape of `test/fixtures/seed_interp/text_from_bytes_static_repro.spl`:
/// a `[u8]`-typed local passed to `text.from_bytes` and the result
/// concatenated. Before `bfe4c8cb879` the call went through the unusable
/// `text_dot_from_bytes` import and the debug seed died with
/// `thread 'simple-main' has overflowed its stack` (rc 139).
/// doc/08_tracking/bug/seed_jit_text_from_bytes_stack_overflow_2026-11-06.md
#[test]
fn text_from_bytes_of_typed_u8_local_concatenates() {
    let source = r#"
fn main() -> i64:
    val b: [u8] = [97u8, 98u8, 99u8]
    val s = "text_from_bytes " + text.from_bytes(b)
    if s != "text_from_bytes abc":
        return 1
    0
"#;
    assert_eq!(run(source), 0);
}
