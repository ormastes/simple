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

const PRODUCER: &str = r#"pub struct Ev:
    n: i64

fn pick(empty: bool) -> Result<Ev?, text>:
    if empty:
        return Ok(None)
    Ok(Some(Ev(n: 7)))
"#;

const MODE_PRODUCER: &str = r#"use pkg.decoy.{Mode}

fn pick_mode(empty: bool) -> Result<Mode?, text>:
    if empty:
        return Ok(None)
    Ok(Some(Mode.Fast))

fn pick_opt(empty: bool) -> Result<Option<Mode>, text>:
    if empty:
        return Ok(None)
    Ok(Some(Mode.Fast))
"#;

const SOME_DECOY: &str = r#"enum Tri:
    Some
    Other
"#;

fn run_classify(modules: &[(&str, &str)], uses: &str, subject: &str) -> i64 {
    let main = format!(
        "{uses}
fn classify(empty: bool) -> i64:
    match {subject}:
        case Err(_): 1
        case Ok(None): 2
        case Ok(Some(_)): 7

fn main() -> i64:
    if classify(true) != 2:
        return 1
    if classify(false) != 7:
        return 2
    0
"
    );
    jit_run_pkg(modules, &main)
}

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

#[test]
fn ok_none_of_pointer_to_enum_owning_none_matches_none_first_and_some_second() {
    // `Mode?` is a pointer to an enum that itself owns `None`; with the `None`
    // arm first, `Ok(Some(Mode.Fast))` used to take the None arm silently.
    let code = run_classify(
        &[("decoy", DECOY), ("mp", MODE_PRODUCER)],
        "use pkg.decoy.{Mode}
use pkg.mp.{pick_mode}",
        "pick_mode(empty)",
    );
    assert_eq!(code, 0);
}

#[test]
fn ok_none_of_explicit_option_of_enum_matches() {
    let code = run_classify(
        &[("decoy", DECOY), ("mp", MODE_PRODUCER)],
        "use pkg.decoy.{Mode}
use pkg.mp.{pick_opt}",
        "pick_opt(empty)",
    );
    assert_eq!(code, 0);
}

#[test]
fn ok_none_matches_when_a_user_enum_declares_some() {
    let code = jit_run_pkg(
        &[("decoy", SOME_DECOY), ("producer", PRODUCER)],
        r#"use pkg.decoy.{Tri}
use pkg.producer.{pick}

fn classify(empty: bool) -> i64:
    match pick(empty):
        case Err(_): 1
        case Ok(None): 2
        case Ok(Some(ev)): ev.n

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

#[test]
fn ok_none_matches_in_a_statement_match_inside_a_loop() {
    let code = jit_run_pkg(
        &[("decoy", DECOY), ("producer", PRODUCER)],
        r#"use pkg.decoy.{Mode}
use pkg.producer.{pick, Ev}

fn scan(flags: [bool]) -> [Ev]?:
    var events: [Ev] = []
    for flag in flags:
        match pick(flag):
            case Err(_): return None
            case Ok(Some(ev)): events.push(ev)
            case Ok(None): ()
    Some(events)

fn main() -> i64:
    val r = scan([true, false, true, false, true])
    if r.is_none():
        return 1
    if r!.len() != 2:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}
