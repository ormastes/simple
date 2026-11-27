//! `Ok(None)` of a `Result<Struct?, text>` must match the `Ok(None)` arm even
//! when ANOTHER enum in the flattened module declares a `None` variant.
//!
//! `is_builtin_optional_variant_name` is a module-wide name test: one user enum
//! with a `None` variant made the nested `None` sub-pattern fall to the
//! discriminant test (`rt_enum_check_variant(slot, OPTION_ID, NONE_DISC)`).
//! The producer builds `Ok(None)` as the raw nil sentinel, so every arm
//! rejected it and the match hit the fail-closed exhaustion panic ("match
//! statement exhausted ..."). Seen live on the SCV cold-init scan
//! (`inventory_events.spl`), whose import closure carries such enums.
//! Bug: doc/08_tracking/bug/native_build_jit_nested_option_result_match_exhausted_2026-11-27.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use std::collections::{HashMap, HashSet};
use std::fs;
use tempfile::tempdir;

fn jit_run_pkg(modules: &[(&str, &str)], main: &str) -> i64 {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    for (name, source) in modules {
        fs::write(pkg.join(format!("{name}.spl")), source).unwrap();
    }
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
    .unwrap_or_else(|error| panic!("HIR lowering failed: {error}"));
    let mir_module = mir::lower_to_mir(&hir_module).unwrap_or_else(|error| panic!("MIR lowering failed: {error}"));
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module)
        .unwrap_or_else(|error| panic!("JIT compile failed: {error}"));
    let code = unsafe { jit.call_i64_void("main").expect("main must execute") };
    simple_compiler::interpreter::set_current_file(None);
    code
}

const DECOY: &str = r#"enum Mode:
    None
    Fast
"#;

const PRODUCER: &str = r#"struct Ev:
    n: i64

fn pick(empty: bool) -> Result<Ev?, text>:
    if empty:
        return Ok(None)
    Ok(Some(Ev(n: 7)))
"#;

#[test]
fn ok_none_matches_the_none_arm_when_a_user_enum_declares_none() {
    let code = jit_run_pkg(
        &[("decoy", DECOY), ("producer", PRODUCER)],
        r#"use pkg.decoy.{Mode}
use pkg.producer.{pick}

fn classify(empty: bool) -> i64:
    match pick(empty):
        case Err(_): 1
        case Ok(Some(ev)): ev.n
        case Ok(None): 2

fn main() -> i64:
    if classify(true) != 2:
        return 1
    if classify(false) != 7:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}
