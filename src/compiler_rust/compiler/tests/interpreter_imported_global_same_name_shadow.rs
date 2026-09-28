//! An imported module global must resolve to the IMPORTED module's symbol,
//! even when an unrelated loaded module defines a global of the same bare
//! name. The flat `MODULE_GLOBALS` map is keyed by bare name, so the last
//! module to load a `g_x` used to shadow the one actually imported — PR #1905
//! hit this as x86_32 `g_vmm` (VirtMemManager32) being read in place of
//! `os.kernel.memory.vmm.g_vmm` ("class VirtMemManager32 has no field named
//! pml4_phys").

use simple_compiler::interpreter;
use std::collections::HashSet;
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

fn run_pkg(c_module: &str, main: &str) -> i32 {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("a.spl"), MOD_A).unwrap();
    fs::write(pkg.join("b.spl"), MOD_B).unwrap();
    fs::write(pkg.join("c.spl"), c_module).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    match result {
        Ok(code) => code,
        Err(error) => panic!("program failed: {error:?}"),
    }
}

#[test]
fn imported_global_read_is_not_shadowed_by_same_named_global() {
    let code = run_pkg(
        r#"use pkg.a.{g_x}

fn c_value() -> i64:
    g_x.a_field
"#,
        r#"use pkg.c.{c_value}
use pkg.b.{b_value}

fn main() -> i32:
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
fn imported_global_writes_do_not_clobber_same_named_global() {
    let code = run_pkg(
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

fn main() -> i32:
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
fn own_module_global_is_not_shadowed_when_imported_module_loads_last() {
    // `b` loads before `c`/`a`, so `a`'s `g_x` is the last bare-name writer.
    let code = run_pkg(
        r#"use pkg.a.{g_x}

fn c_value() -> i64:
    g_x.a_field
"#,
        r#"use pkg.b.{b_value}
use pkg.c.{c_value}

fn main() -> i32:
    if b_value() != 22:
        return 1
    if c_value() != 11:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}
