//! A free function imported THROUGH a re-export facade must bind to the module
//! that declares it, even when another flattened module declares a same-named
//! function.
//!
//! `app/io/file_ops.spl` is the live shape (`export use std...file_ops.*`):
//! with ~15 same-named `file_exists` definitions in the native-build closure,
//! HIR's owner-exact lookup (`resolve_flatten_owned_callable`) only accepted an
//! import binding whose source owner itself DECLARES the name. A facade
//! declares nothing, so the lookup fell back to the bare name -- the
//! "last definition" of an unrelated module -- and the JIT silently called the
//! wrong function (interpreter: `user=1`, JIT: `user=2`). The interpreter twin
//! (`interpreter_call::import_bound_candidate`) already walks the facade chain.
//! Runs through the real flatten path (`load_module_with_imports`).

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

/// `real.ops.pick` returns 1; `other.x.pick` returns 2 and is called by
/// `other_val`; `user.u.user_val` calls `pick` imported via `facade_rel`.
/// `main` returns `user_val() * 10 + other_val()`; correct binding is 12.
fn run(facades: &[(&str, &str)], user_import: &str) -> i64 {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = dir.path().join("src");
    write(&src, "real/ops.spl", "pub fn pick() -> i64:\n    1\n");
    for (rel, body) in facades {
        write(&src, rel, body);
    }
    write(&src, "other/x.spl", "pub fn pick() -> i64:\n    2\n\npub fn other_val() -> i64:\n    pick()\n");
    write(
        &src,
        "user/u.spl",
        &format!("use {user_import}.{{pick}}\n\npub fn user_val() -> i64:\n    pick()\n"),
    );
    // `other` is imported LAST so its `pick` is the bare-name "last
    // definition" -- the one the unfixed lookup wrongly bound.
    let main = src.join("main.spl");
    fs::write(
        &main,
        "use user.u.{user_val}\nuse other.x.{other_val}\n\nfn main() -> i64:\n    user_val() * 10 + other_val()\n",
    )
    .unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main, &mut HashSet::new())
        .expect("flatten");
    let hir_module = hir::lower(&module).expect("HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("MIR");
    let mut jit = JitCompiler::new_static().expect("JIT");
    jit.compile_module(&mir_module).expect("JIT compile");
    unsafe { jit.call_i64_void("main").expect("run") }
}

#[test]
fn direct_import_binds_declaring_module() {
    // Control: no facade. Already correct before the fix.
    assert_eq!(run(&[], "real.ops"), 12);
}

#[test]
fn glob_reexport_facade_binds_declaring_module() {
    assert_eq!(run(&[("facade/ops.spl", "export use real.ops.*\n")], "facade.ops"), 12);
}

#[test]
fn explicit_reexport_facade_binds_declaring_module() {
    assert_eq!(run(&[("facade/ops.spl", "export use real.ops.{pick}\n")], "facade.ops"), 12);
}

#[test]
fn two_hop_reexport_facade_chain_binds_declaring_module() {
    assert_eq!(
        run(
            &[
                ("facade/ops.spl", "export use real.ops.*\n"),
                ("outer/ops.spl", "export use facade.ops.{pick}\n"),
            ],
            "outer.ops",
        ),
        12
    );
}
