//! An extern defined only in `elf_utils` (not in RUNTIME_SYMBOL_NAMES) is bound
//! by `JitCompiler::with_provider`'s elf_utils lookup fn, so the JIT calls the
//! real function instead of a NULL GOT slot. Same values as the interpreter:
//! 3 live handles, then each freed.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

#[test]
fn jit_calls_elf_utils_only_cranelift_extern() {
    let source = r#"
extern fn rt_cranelift_new_module(name_ptr: i64, name_len: i64, target: i64) -> i64
extern fn rt_cranelift_free_module(module: i64)
extern fn rt_string_data(value: text) -> i64
extern fn rt_string_len(value: text) -> i64

fn main() -> i64:
    val name = "jit_elf_only"
    val ptr: i64 = rt_string_data(name)
    val len: i64 = rt_string_len(name)
    var live = 0
    var i = 0
    while i < 3:
        val m = rt_cranelift_new_module(ptr, len, -1)
        if m > 0:
            live = live + 1
        rt_cranelift_free_module(m)
        i = i + 1
    live * 10 + rt_cranelift_new_module(0, 0, -1)
"#;
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    // An empty name is rejected (0), so 3 live handles read 30.
    assert_eq!(unsafe { jit.call_i64_void("main").expect("main must execute") }, 30);
}
