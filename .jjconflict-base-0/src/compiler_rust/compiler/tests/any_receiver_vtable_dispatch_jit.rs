//! A bare method call on an ERASED receiver (`block_def: Any`, or a
//! trait-typed parameter) whose candidate implementors all carry a trait
//! vtable must be JIT-compiled as a runtime type switch on the receiver's
//! vtable identity — no `[CODEGEN-AMBIGUOUS-METHOD]` bail of the whole module.
//!
//! Pre-fix: `JitCompiler::compile_module` refused the module ("bare method
//! 'kind' has 3 candidates ... refusing to pick shortest"), which dropped the
//! ENTIRE stage1 compiler (`15.blocks/blocks/registry.spl` `BlockRegistry.register`
//! with `block_def: Any`, and `obj_taker.spl` `smf_reader: SmfReader`) onto the
//! tree-walking interpreter. See
//! doc/08_tracking/bug/jit_any_receiver_ambiguous_method_bails_stage1_2026-08-22.md.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    // The load-bearing assertion: no bail. Pre-fix this is
    // Err("...[CODEGEN-AMBIGUOUS-METHOD]...").
    jit.compile_module(&mir_module)
        .expect("bare method on an Any receiver with vtable-carrying candidates must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn any_receiver_method_dispatches_by_vtable_identity() {
    // The stage1 BlockRegistry shape: N trait implementors, a registry that
    // takes `Any` and calls a bare method on it.
    let source = r#"
trait Kinded:
    fn kind_code() -> i64:
        pass
    fn weight(n: i64) -> i64:
        pass

struct ShellDef(Kinded):
    fn kind_code() -> i64: 1
    fn weight(n: i64) -> i64: n + 1

struct SqlDef(Kinded):
    fn kind_code() -> i64: 2
    fn weight(n: i64) -> i64: n * 10

struct JsonDef(Kinded):
    fn kind_code() -> i64: 3
    fn weight(n: i64) -> i64: n - 1

fn code_of(block_def: Any) -> i64:
    block_def.kind_code()

fn weigh(block_def: Any, n: i64) -> i64:
    block_def.weight(n)

fn main() -> i64:
    if code_of(ShellDef()) != 1: return 1
    if code_of(SqlDef()) != 2: return 2
    if code_of(JsonDef()) != 3: return 3
    if weigh(ShellDef(), 4) != 5: return 4
    if weigh(SqlDef(), 4) != 40: return 5
    if weigh(JsonDef(), 4) != 3: return 6
    0
"#;
    assert_eq!(run(source), 0);
}

#[test]
fn trait_typed_param_receiver_dispatches_by_vtable_identity() {
    // The obj_taker shape: `smf_reader: SmfReader` trait-typed parameter.
    let source = r#"
trait Reader:
    fn lookup(n: i64) -> i64:
        pass

struct MemReader(Reader):
    base: i64
    fn lookup(n: i64) -> i64: self.base + n

struct FileReader(Reader):
    fn lookup(n: i64) -> i64: 1000 + n

fn take(reader: Reader, n: i64) -> i64:
    reader.lookup(n)

fn main() -> i64:
    if take(MemReader(base: 5), 3) != 8: return 1
    if take(FileReader(), 4) != 1004: return 2
    0
"#;
    assert_eq!(run(source), 0);
}
