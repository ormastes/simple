//! A function reached only through a single-symbol `pub use a.b.f` (or the
//! `common use` / comma multi-use forms) of a module FILE must be flattened
//! into the JIT unit, exactly like a plain `use a.b.f`.
//!
//! Live shape: `src/os/apps/smux/runtime_binding_owner_v3.spl` re-exports
//! `smux_runtime_binding_{bind,prepare,inspect}_v3` with
//! `pub use os.apps.smux.runtime_binding_bind_v3.smux_runtime_binding_bind_v3`.
//! The `UseStmt` branch of `load_module_with_imports_internal` flattened that
//! form (`single_import_targets_module_file`). The `ExportUseStmt`,
//! `CommonUseStmt` and `MultiUse` branches did not, so the body never reached
//! MIR and caret's JIT unit failed with "unresolved external symbol ...
//! (cross-module Simple function ...)".
//! Design: doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md (rows 2-4)

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};

fn write(root: &Path, rel: &str, body: &str) {
    let path = root.join(rel);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, body).unwrap();
}

fn run(files: &[(&str, &str)], main_body: &str) -> Result<i64, String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = dir.path().join("src");
    for (rel, body) in files {
        write(&src, rel, body);
    }
    let main = src.join("main.spl");
    fs::write(&main, main_body).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main, &mut HashSet::new())
        .map_err(|e| format!("flatten: {e}"))?;
    let hir_module = hir::lower(&module).map_err(|e| format!("HIR: {e}"))?;
    let mir_module = mir::lower_to_mir(&hir_module).map_err(|e| format!("MIR: {e}"))?;
    let mut jit = JitCompiler::new_static().map_err(|e| format!("JIT: {e}"))?;
    jit.compile_module(&mir_module).map_err(|e| format!("JIT compile: {e}"))?;
    unsafe { jit.call_i64_void("main").map_err(|e| format!("run: {e}")) }
}

const OPS: (&str, &str) = ("real/ops.spl", "pub fn pick() -> i64:\n    41\n");
const TWO: (&str, &str) = ("real/two.spl", "pub fn other() -> i64:\n    1\n");

#[test]
fn pub_use_single_symbol_of_module_file_is_flattened() {
    let facade = ("facade/ops.spl", "pub use real.ops.pick\n");
    assert_eq!(
        run(&[OPS, facade], "use facade.ops.{pick}\n\nfn main() -> i64:\n    pick() + 1\n"),
        Ok(42)
    );
}

#[test]
fn common_use_single_symbol_of_module_file_is_flattened() {
    let facade = ("facade/ops.spl", "common use real.ops.pick\n\npub fn via_common() -> i64:\n    pick() + 1\n");
    assert_eq!(
        run(&[OPS, facade], "use facade.ops.{via_common}\n\nfn main() -> i64:\n    via_common()\n"),
        Ok(42)
    );
}

#[test]
fn multi_use_single_symbols_of_module_files_are_flattened() {
    let facade = ("facade/ops.spl", "use real.ops.pick, real.two.other\n\npub fn both() -> i64:\n    pick() + other()\n");
    assert_eq!(
        run(&[OPS, TWO, facade], "use facade.ops.{both}\n\nfn main() -> i64:\n    both()\n"),
        Ok(42)
    );
}

/// A non-`__init__` aggregator re-exporting two siblings that each declare a
/// private `_h`: flattening both must keep each caller bound to its own helper.
#[test]
fn aggregator_reexport_keeps_same_named_private_helpers_owner_exact() {
    let a = ("pa/a.spl", "fn _h() -> i64:\n    1\n\npub fn fa() -> i64:\n    _h()\n");
    let b = ("pb/b.spl", "fn _h() -> i64:\n    2\n\npub fn fb() -> i64:\n    _h()\n");
    let agg = ("agg/all.spl", "pub use pa.a.fa\npub use pb.b.fb\n");
    assert_eq!(
        run(&[a, b, agg], "use agg.all.{fa, fb}\n\nfn main() -> i64:\n    fa() * 10 + fb()\n"),
        Ok(12)
    );
}
