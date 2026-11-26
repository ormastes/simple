//! `impl Trait for text` methods must be reachable from a `text` receiver
//! under the JIT. Pre-fix the receiver was qualified as `str.m` (the builtin
//! name of TypeId::STRING) while the impl registered `text.m`, so JIT dispatch
//! failed ("Function 'str.probe' not found").
//! doc/08_tracking/bug/primitive_receiver_trait_impl_dispatch_2026-08-07.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

#[test]
fn text_and_i64_trait_impls_dispatch_under_jit() {
    let source = r#"
trait MarkerProbe:
    fn probe() -> i64

impl MarkerProbe for i64:
    fn probe() -> i64:
        self + 100

impl MarkerProbe for text:
    fn probe() -> i64:
        self.len() + 1000

fn main() -> i64:
    val a: i64 = 5
    val s: text = "abc"
    if a.probe() != 105: return 1
    if s.probe() != 1003: return 2
    if s.len() != 3: return 3
    0
"#;
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower_lenient(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    assert_eq!(unsafe { jit.call_i64_void("main").expect("main must execute") }, 0);
}

#[test]
fn text_trait_hash_impl_dispatches_instead_of_rt_hash_text() {
    let source = r#"
trait HashProbe:
    fn hash() -> i64

impl HashProbe for text:
    fn hash() -> i64:
        self.len() + 7000

fn main() -> i64:
    val s: text = "hello"
    if s.hash() != 7005: return 1
    if "ab".hash() != 7002: return 2
    0
"#;
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower_lenient(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    assert_eq!(unsafe { jit.call_i64_void("main").expect("main must execute") }, 0);
}

#[test]
fn text_hash_without_trait_impl_keeps_rt_hash_text_jit_parity() {
    let source = r#"
fn main() -> i64:
    val s: text = "hello"
    s.hash()
"#;
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower_lenient(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    assert_eq!(
        unsafe { jit.call_i64_void("main").expect("main must execute") },
        -6615550055289275125i64
    );
}
