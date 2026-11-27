//! HIR: a method call on a flat-nullable `T?` receiver (`var v = opt.?`) must
//! take its return type from `T.method`, not from the shortest-named owner of
//! any same-named method. Before the fix `a.finish()` below was typed as
//! `Eng.finish() -> void` (shorter owner than `Adapter.finish`), and the
//! ambiguous `evidence.ready` failed HIR lowering with
//! `Cannot infer field type: struct 'Void' field 'ready'`, dropping the whole
//! module (Engine3D font path) to the interpreter.
//! Bug: doc/08_tracking/bug/seed_jit_nullable_receiver_method_typed_by_shorter_owner_2026-11-04.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

const SRC: &str = "class Ev:
    ready: bool
    n: i64

class Other:
    ready: i64

class Adapter:
    ok: bool
    me finish() -> Ev:
        Ev(ready: self.ok, n: 7)

class Eng:
    _ad: Adapter? = nil
    _n: i64 = 0
    me finish():
        val active = self._ad
        if active != nil:
            val a = active.?
            val evidence = a.finish()
            if evidence.ready:
                self._n = evidence.n

fn main() -> i64:
    var e = Eng(_ad: Adapter(ok: true), _n: 0)
    e.finish()
    e._n
";

#[test]
fn nullable_receiver_method_uses_inner_owner_return_type() {
    let ast = Parser::new(SRC).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("must lower to HIR (no struct 'Void' field error)");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    assert_eq!(v, 7);
}
