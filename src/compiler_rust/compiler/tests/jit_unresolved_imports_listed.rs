//! The JIT's NULL-jump guard must name EVERY directly-called unresolved import
//! in one refusal, not only the first.
//!
//! Caret hid three unresolved smux functions behind each other
//! (`smux_runtime_binding_{bind,prepare,inspect}_v3`): the guard returned the
//! first name only, so each fix exposed the next.
//! Design: doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md (step 3)
//! (`codegen/jit_tests.rs` holds the single-name tests but is x86_64-only.)

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

#[test]
fn unresolved_imports_are_all_named_in_one_refusal() {
    simple_runtime::register_static_runtime_symbols();
    let source = r#"
@unsafe(reason: "test unresolved imports", capabilities: [ffi])
extern fn simple_seed_xmodule_first_zzqq(x: i64) -> i64
@unsafe(reason: "test unresolved imports", capabilities: [ffi])
extern fn simple_seed_xmodule_second_zzqq(x: i64) -> i64

fn caller() -> i64:
    simple_seed_xmodule_first_zzqq(1) + simple_seed_xmodule_second_zzqq(2)
"#;
    let ast = Parser::new(source).parse().expect("parse fixture");
    let hir_module = hir::lower(&ast).expect("HIR lower fixture");
    let mir_module = mir::lower_to_mir(&hir_module).expect("MIR lower fixture");
    let mut jit = JitCompiler::new_static().expect("create static JIT");
    let err = format!("{:?}", jit.compile_module(&mir_module).expect_err("must refuse"));
    for name in ["simple_seed_xmodule_first_zzqq", "simple_seed_xmodule_second_zzqq"] {
        assert!(err.contains(name), "refusal must name `{name}`, got: {err}");
    }
    assert!(err.contains("cross-module Simple function"), "cause must stay classified: {err}");
}
