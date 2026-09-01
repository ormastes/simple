//! A function or method declared `-> ()` must RETURN. It must not trap.
//!
//! Pre-fix, `()` parsed to `Type::Tuple(vec![])` (parser_types.rs:756) and the
//! HIR type resolver registered that as `HirType::Tuple([])` — a TypeId that is
//! NOT `TypeId::VOID`. Codegen's `Terminator::Return(None)` arm
//! (codegen/instr/body.rs) tests `func.return_type == TypeId::VOID` to decide
//! whether a value-less return is legitimate, so every `-> ()` function fell
//! through to the fail-fast arm and was emitted with a terminating `trap`
//! (`ud2` on x86_64) and no `ret` instruction at all.
//!
//! Hosted, that is a fatal SIGILL. In-guest on SimpleOS it is a live fault: the
//! mcp component row died inside `DispatchRegistry.register`, declared
//! `me register(entry: DispatchEntry) -> ():` in
//! src/lib/nogc_async_mut/mcp/dispatch.spl:89. The x86_64 serial transcript read
//! `FAULT @ 0x0000000008005e61`, which objdump maps exactly onto that function's
//! terminating `ud2`, immediately after the store of its last statement.
//!
//! Fix: the resolver maps an empty `Type::Tuple` to `TypeId::VOID`, which is the
//! codebase's own stated home for unit ("Use TypeId::VOID for empty/unit types",
//! type_system.rs:93) and already where the bare name `unit` resolves.
//!
//! These tests fail pre-fix by trapping (SIGILL) rather than by returning a
//! wrong number, so they are run in a child process would-be; the JIT harness
//! surfaces the trap as a process-level fault, which is itself the signal.

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

/// The exact shape of `DispatchRegistry.register`: a `me` method annotated
/// `-> ()` whose body ends in a field mutation, called for its effect.
#[test]
fn unit_returning_method_returns_instead_of_trapping() {
    let source = r#"
class Counter:
    var n: i64

    me bump() -> ():
        self.n = self.n + 1

fn main() -> i64:
    var c = Counter(n: 0)
    c.bump()
    c.bump()
    if c.n != 2: return 1
    0
"#;
    assert_eq!(run(source), 0);
}

/// A free function spelled `-> ()`. The unannotated form already worked (it
/// resolves to VOID directly), so this pins the SPELLING, which is what broke.
#[test]
fn unit_returning_free_function_returns_instead_of_trapping() {
    let source = r#"
var total: i64 = 0

fn add_to_total(x: i64) -> ():
    total = total + x

fn main() -> i64:
    add_to_total(40)
    add_to_total(2)
    if total != 42: return 1
    0
"#;
    assert_eq!(run(source), 0);
}

/// `()` and the unannotated form must agree — before the fix they resolved to
/// two different TypeIds, only one of which codegen recognised as unit.
#[test]
fn explicit_unit_and_implicit_void_agree() {
    let source = r#"
var a: i64 = 0
var b: i64 = 0

fn explicit(x: i64) -> ():
    a = a + x

fn implicit(x: i64):
    b = b + x

fn main() -> i64:
    explicit(21)
    implicit(21)
    if a != b: return 1
    if a != 21: return 2
    0
"#;
    assert_eq!(run(source), 0);
}
