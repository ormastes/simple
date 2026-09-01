//! A bare method call on a TYPE-ERASED receiver whose name collides with the
//! builtin-collection set (`find`, `get`, `has`, `remove`, `slice`, ...) must
//! NOT be claimed unconditionally by the builtin when the concrete receiver is
//! a CLASS instance that defines that method itself.
//!
//! Pre-fix, `codegen/instr/closures_structs.rs` routed any BARE call whose
//! (name, arity) is in `is_bare_builtin_collection_method` straight to the
//! builtin — before user-method resolution ever ran. `rt_find` then untags the
//! receiver and reads a 32-bit type header at offset 0, which class instances
//! (plain `rt_alloc`, fields at 0/8/16, tagged as heap) do not carry.
//!
//! On riscv64/freestanding that misread TRAPS and reboots the guest (goal item
//! 3, `mcp` row). On x86_64/aarch64 it is LATENT but equally wrong: the
//! builtin answers its `-1` miss sentinel instead of running the user method,
//! silently. This test asserts the VALUE, so it is red on every arch.
//!
//! Contrast that pinned the cause: `register` is absent from that set, so the
//! SAME receiver resolves correctly for it.
//!
//! See doc/08_tracking/bug/riscv64_erased_receiver_routes_class_method_to_rt_find_2026-08-31.md

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

/// The defect, minimal: an erased class receiver, a user method named `find`.
#[test]
fn erased_class_receiver_runs_its_own_find_not_the_builtin() {
    let source = r#"
struct Registry:
    var seed: i64

    fn find(key: i64) -> i64:
        return me.seed + key

fn make() -> Registry:
    return Registry(40)

fn main() -> i64:
    var reg: Any = make()
    return reg.find(2)
"#;
    // Pre-fix: the bare `find` is claimed by the builtin, which answers its
    // -1 miss sentinel on a receiver it cannot parse (or traps outright).
    assert_eq!(
        run(source),
        42,
        "an erased CLASS receiver must run its own `find`, not the builtin collection `find`"
    );
}

/// The control that pinned the cause: a name OUTSIDE the builtin set already
/// resolves correctly through the same erased receiver. Guards against a fix
/// that regresses ordinary erased-receiver method resolution.
#[test]
fn erased_class_receiver_control_name_outside_builtin_set() {
    let source = r#"
struct Registry:
    var seed: i64

    fn register(key: i64) -> i64:
        return me.seed + key

fn make() -> Registry:
    return Registry(40)

fn main() -> i64:
    var reg: Any = make()
    return reg.register(2)
"#;
    assert_eq!(
        run(source),
        42,
        "`register` is not in the builtin set and must already work"
    );
}

/// Bug #62 regression guard, the other direction: a GENUINELY erased builtin
/// collection receiver must still reach the builtin, even when a same-named
/// user method is linked into the module. This is the case the unconditional
/// routing existed to protect, and the fix must not give it away.
#[test]
fn erased_builtin_collection_receiver_still_reaches_the_builtin() {
    let source = r#"
struct Shadow:
    var seed: i64

    fn find(key: i64) -> i64:
        return 999

fn main() -> i64:
    val unused = Shadow(1)
    val text = "hello world"
    var erased: Any = text
    # `find` on a text receiver is the builtin: raw index of the needle.
    return erased.find("world")
"#;
    assert_eq!(
        run(source),
        6,
        "a genuine erased TEXT receiver must still reach the builtin `find` (bug #62)"
    );
}
