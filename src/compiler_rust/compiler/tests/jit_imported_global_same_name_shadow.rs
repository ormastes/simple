//! JIT twin of `interpreter_imported_global_same_name_shadow.rs` (PR #1936).
//!
//! An imported module global must resolve to the IMPORTED module's symbol in
//! the codegen lane too. `load_module_with_imports` flattens every module into
//! one unit, and HIR lowering registered module globals by bare name, so two
//! modules each defining `g_x` collapsed onto one symbol: a function of `c`
//! (which imports `a.g_x`) read `b`'s `g_x` and failed with
//! `Cannot infer field type: struct 'BoxB' field 'a_field'`, de-JITting the
//! whole module to the interpreter.
//!
//! These tests drive exactly the `run_file_jit` pipeline (load + flatten,
//! lenient HIR lowering with the project hint, MIR, Cranelift JIT) and fail if
//! any stage errors -- i.e. if the driver would have fallen back.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use std::collections::{HashMap, HashSet};
use std::fs;
use tempfile::tempdir;

const MOD_A: &str = r#"class BoxA:
    a_field: i64

impl BoxA:
    me bump() -> i64:
        self.a_field = self.a_field + 1
        self.a_field

var g_x: BoxA = BoxA(a_field: 11)
"#;

const MOD_B: &str = r#"class BoxB:
    b_field: i64

var g_x: BoxB = BoxB(b_field: 22)

fn b_value() -> i64:
    g_x.b_field
"#;

fn jit_run_pkg(c_module: &str, main: &str) -> i64 {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("a.spl"), MOD_A).unwrap();
    fs::write(pkg.join("b.spl"), MOD_B).unwrap();
    fs::write(pkg.join("c.spl"), c_module).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();

    simple_compiler::interpreter::set_current_file(Some(main_path.clone()));
    let mut ast =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    simple_compiler::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut ast);
    let project_hint = simple_compiler::pipeline::native_single_file_project_hint(&main_path);
    let hir_module = hir::lower_with_context_lenient_project_hint_and_duplicate_structs(
        &ast,
        &main_path,
        project_hint.as_deref(),
        HashMap::new(),
    )
    .unwrap_or_else(|error| panic!("HIR lowering failed (run_file_jit would de-JIT): {error}"));
    let mir_module = mir::lower_to_mir(&hir_module)
        .unwrap_or_else(|error| panic!("MIR lowering failed (run_file_jit would de-JIT): {error}"));
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module)
        .unwrap_or_else(|error| panic!("JIT compile failed (run_file_jit would de-JIT): {error}"));
    let code = unsafe { jit.call_i64_void("main").expect("main must execute") };
    simple_compiler::interpreter::set_current_file(None);
    code
}

#[test]
fn jit_imported_global_read_is_not_shadowed_by_same_named_global() {
    let code = jit_run_pkg(
        r#"use pkg.a.{g_x}

fn c_value() -> i64:
    g_x.a_field
"#,
        r#"use pkg.c.{c_value}
use pkg.b.{b_value}

fn main() -> i64:
    if c_value() != 11:
        return 1
    if b_value() != 22:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn jit_imported_global_writes_do_not_clobber_same_named_global() {
    let code = jit_run_pkg(
        r#"use pkg.a.{g_x}

fn c_field_write() -> i64:
    g_x.a_field = 40
    g_x.a_field

fn c_bump() -> i64:
    g_x.bump()

fn c_value() -> i64:
    g_x.a_field
"#,
        r#"use pkg.c.{c_field_write, c_bump, c_value}
use pkg.b.{b_value}

fn main() -> i64:
    if c_field_write() != 40:
        return 1
    if b_value() != 22:
        return 2
    if c_bump() != 41:
        return 3
    if b_value() != 22:
        return 4
    if c_value() != 41:
        return 5
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn jit_own_module_global_is_not_shadowed_when_imported_module_loads_last() {
    // `b` loads before `c`/`a`, so `a`'s `g_x` is the last bare-name definition.
    let code = jit_run_pkg(
        r#"use pkg.a.{g_x}

fn c_value() -> i64:
    g_x.a_field
"#,
        r#"use pkg.b.{b_value}
use pkg.c.{c_value}

fn main() -> i64:
    if b_value() != 22:
        return 1
    if c_value() != 11:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn jit_bare_assignment_to_imported_scalar_global_targets_its_owner() {
    // Scalar globals take the const-init path and a bare `g_n = v` store, not
    // a field write: both must land in the imported module's slot.
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("a.spl"), "var g_n: i64 = 1\n\nfn a_value() -> i64:\n    g_n\n").unwrap();
    fs::write(pkg.join("b.spl"), "var g_n: i64 = 2\n\nfn b_value() -> i64:\n    g_n\n").unwrap();
    fs::write(
        pkg.join("c.spl"),
        "use pkg.a.{g_n}\n\nfn c_set(v: i64):\n    g_n = v\n\nfn c_value() -> i64:\n    g_n\n",
    )
    .unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(
        &main_path,
        r#"use pkg.a.{a_value}
use pkg.b.{b_value}
use pkg.c.{c_set, c_value}

fn main() -> i64:
    if c_value() != 1:
        return 1
    c_set(7)
    if a_value() != 7:
        return 2
    if b_value() != 2:
        return 3
    if c_value() != 7:
        return 4
    0
"#,
    )
    .unwrap();
    let ast =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    let hir_module = hir::lower_with_context_lenient_project_hint_and_duplicate_structs(
        &ast,
        &main_path,
        simple_compiler::pipeline::native_single_file_project_hint(&main_path).as_deref(),
        HashMap::new(),
    )
    .unwrap_or_else(|error| panic!("HIR lowering failed: {error}"));
    let mir_module = mir::lower_to_mir(&hir_module).unwrap_or_else(|error| panic!("MIR lowering failed: {error}"));
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module)
        .unwrap_or_else(|error| panic!("JIT compile failed: {error}"));
    assert_eq!(unsafe { jit.call_i64_void("main").expect("main must execute") }, 0);
}
