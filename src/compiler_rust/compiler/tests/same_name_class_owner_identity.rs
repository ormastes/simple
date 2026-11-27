//! Owner-module identity for same-named CLASSES in the flattened run lane.
//!
//! Two modules each declare `class Thing` (same field layout, different
//! methods/statics). The entry imports `pa.Thing` plainly and `pb.Thing`
//! through an alias (`as Legacy`) or through its module namespace
//! (`pb.Thing`). Owner decision 2026-11-27: a class is identified by its
//! owner module, not its bare name, so `Legacy.create()`, `pb.Thing.tag()`
//! and every self-method call on a `pb` instance must run `pb`'s bodies --
//! in the interpreter AND in the JIT.
//!
//! Bug: doc/08_tracking/bug/db/interpreter_same_name_class_method_dispatch_collision_2026_11_26.sdn
//! (both lanes printed `ln=1 lsize=24 b.compile=24`, i.e. `pa`'s class).

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use tempfile::TempDir;

const PA: &str = r#"class Thing:
    n: i64

    static fn create() -> Thing:
        Thing(n: 1)

    static fn tag() -> i64:
        100

    fn size() -> i64:
        24

    fn compile() -> i64:
        self.size()
"#;

const PB: &str = r#"class Thing:
    n: i64

    static fn create() -> Thing:
        Thing(n: 2)

    static fn tag() -> i64:
        200

    fn size() -> i64:
        10

    fn compile() -> i64:
        1000 + self.size()
"#;

/// Shared body: every check returns a distinct nonzero code on failure.
const CHECKS: &str = r#"
    val a = Thing.create()
    val l = LEGACY.create()
    if a.n != 1:
        return 1
    if a.compile() != 24:
        return 2
    if Thing.tag() != 100:
        return 3
    if l.n != 2:
        return 4
    if l.size() != 10:
        return 5
    if l.compile() != 1010:
        return 6
    if LEGACY.tag() != 200:
        return 7
    0
"#;

fn write_pkg(main: &str) -> (TempDir, PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("pa.spl"), PA).unwrap();
    fs::write(pkg.join("pb.spl"), PB).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();
    (dir, main_path)
}

fn main_source(imports: &str, legacy: &str) -> String {
    format!("{imports}\n\nfn main() -> i64:{}", CHECKS.replace("LEGACY", legacy))
}

fn jit_run(main: &str) -> i64 {
    let (_dir, main_path) = write_pkg(main);
    interpreter::set_current_file(Some(main_path.clone()));
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
    interpreter::set_current_file(None);
    code
}

fn interp_run(main: &str) -> i32 {
    let (_dir, main_path) = write_pkg(main);
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    interpreter::set_current_file(Some(main_path.clone()));
    let ast =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    let code = interpreter::evaluate_module(&ast.items).unwrap_or_else(|error| panic!("interpreter failed: {error}"));
    interpreter::set_current_file(None);
    code
}

fn alias_main() -> String {
    main_source("use pkg.pa.Thing\nuse pkg.pb.Thing as Legacy", "Legacy")
}

fn braced_alias_main() -> String {
    main_source("use pkg.pa.{Thing}\nuse pkg.pb.{Thing as Legacy}", "Legacy")
}

fn namespace_main() -> String {
    main_source("use pkg.pa.Thing\nuse pkg.pb", "pb.Thing")
}

#[test]
fn interpreter_alias_resolves_to_owner_class() {
    assert_eq!(interp_run(&alias_main()), 0);
}

#[test]
fn interpreter_braced_alias_resolves_to_owner_class() {
    assert_eq!(interp_run(&braced_alias_main()), 0);
}

#[test]
fn interpreter_namespace_qualified_class_resolves_to_owner() {
    assert_eq!(interp_run(&namespace_main()), 0);
}

#[test]
fn jit_alias_resolves_to_owner_class() {
    assert_eq!(jit_run(&alias_main()), 0);
}

#[test]
fn jit_braced_alias_resolves_to_owner_class() {
    assert_eq!(jit_run(&braced_alias_main()), 0);
}

#[test]
fn jit_namespace_qualified_class_resolves_to_owner() {
    assert_eq!(jit_run(&namespace_main()), 0);
}

/// A third module importing `pb.Thing` under an alias, used through a param
/// annotation, a typed local and a static call; plus a same-layout type alias
/// (which must neither refuse the JIT nor fail the interpreter).
const PC: &str = r#"use pkg.pb.{Thing as Old}

fn old_size(t: Old) -> i64:
    val x: Old = t
    x.compile()

fn old_make() -> Old:
    Old.create()
"#;

fn write_extra(main: &str) -> (TempDir, PathBuf) {
    let (dir, main_path) = write_pkg(main);
    fs::write(main_path.parent().unwrap().join("pc.spl"), PC).unwrap();
    (dir, main_path)
}

const EXTRA_MAIN: &str = r#"use pkg.pa.Thing
use pkg.pc.{old_size, old_make}

type Shared = Thing

fn main() -> i64:
    val o = old_make()
    if o.n != 2:
        return 11
    if old_size(o) != 1010:
        return 12
    val s: Shared = Thing.create()
    if s.compile() != 24:
        return 13
    0
"#;

const ENTRY_OWN_MAIN: &str = r#"use pkg.pb.Thing as Legacy

class Thing:
    n: i64

    static fn create() -> Thing:
        Thing(n: 7)

    fn size() -> i64:
        70

fn main() -> i64:
    if Thing.create().size() != 70:
        return 21
    if Legacy.create().compile() != 1010:
        return 22
    0
"#;

fn jit_run_extra(main: &str) -> i64 {
    let (_dir, main_path) = write_extra(main);
    interpreter::set_current_file(Some(main_path.clone()));
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
    let mir_module = mir::lower_to_mir(&hir_module).unwrap_or_else(|error| panic!("MIR lowering failed: {error}"));
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).unwrap_or_else(|error| panic!("JIT compile failed: {error}"));
    let code = unsafe { jit.call_i64_void("main").expect("main must execute") };
    interpreter::set_current_file(None);
    code
}

fn interp_run_extra(main: &str) -> i32 {
    let (_dir, main_path) = write_extra(main);
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    interpreter::set_current_file(Some(main_path.clone()));
    let ast =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    let code = interpreter::evaluate_module(&ast.items).unwrap_or_else(|error| panic!("interpreter failed: {error}"));
    interpreter::set_current_file(None);
    code
}

#[test]
fn interpreter_third_module_alias_annotation_and_type_alias() {
    assert_eq!(interp_run_extra(EXTRA_MAIN), 0);
}

#[test]
fn jit_third_module_alias_annotation_and_type_alias() {
    assert_eq!(jit_run_extra(EXTRA_MAIN), 0);
}

#[test]
fn interpreter_entry_declared_class_keeps_its_own_identity() {
    assert_eq!(interp_run_extra(ENTRY_OWN_MAIN), 0);
}

#[test]
fn jit_entry_declared_class_keeps_its_own_identity() {
    assert_eq!(jit_run_extra(ENTRY_OWN_MAIN), 0);
}

// ---------------------------------------------------------------------------
// Renamed instances inside function bodies (Fable review 2026-11-27): a
// struct pattern, a generic same-named struct and same-module overloads must
// still see an owner-exact instance as their own type.

const QA: &str = r#"
struct P:
    x: i64

struct Box<T>:
    item: T

fn qa_make() -> P:
    P(x: 3)

fn qa_px(p: P) -> i64:
    match p:
        case P { x }:
            x
        case _:
            -1

fn qa_box() -> i64:
    val b: Box<i64> = Box(item: 4)
    match b:
        case Box { item }:
            item + 100
        case _:
            -1

fn qa_any(p) -> i64:
    match p:
        case P { x }:
            x
        case _:
            -1
"#;

const QB: &str = r#"
struct P:
    x: i64

struct Box<T>:
    item: T

class Thing:
    n: i64

fn qb_make() -> P:
    P(x: 5)

fn qb_px(p: P) -> i64:
    match p:
        case P { x }:
            x
        case _:
            -1

fn qb_box() -> i64:
    val b: Box<i64> = Box(item: 6)
    match b:
        case Box { item }:
            item + 200
        case _:
            -1

fn show(n: i64) -> i64:
    22

fn show(t: Thing) -> i64:
    11

fn qb_show() -> i64:
    show(Thing(n: 1)) * 100 + show(7)
"#;

const QC: &str = "class Thing:\n    n: i64\n";

fn write_modules(modules: &[(&str, &str)], main: &str) -> (TempDir, PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    for (name, source) in modules {
        fs::write(pkg.join(format!("{name}.spl")), source).unwrap();
    }
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();
    (dir, main_path)
}

fn interp_run_modules(modules: &[(&str, &str)], main: &str) -> i32 {
    let (_dir, main_path) = write_modules(modules, main);
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    interpreter::set_current_file(Some(main_path.clone()));
    let ast =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    let code = interpreter::evaluate_module(&ast.items).unwrap_or_else(|error| panic!("interpreter failed: {error}"));
    interpreter::set_current_file(None);
    code
}

const PATTERN_MAIN: &str = r#"use pkg.qa.{qa_make, qa_px, qa_box}
use pkg.qb.{qb_make, qb_px, qb_box}

fn main() -> i64:
    if qa_px(qa_make()) != 3:
        return 1
    if qb_px(qb_make()) != 5:
        return 2
    if qa_box() != 104:
        return 3
    if qb_box() != 206:
        return 4
    0
"#;

#[test]
fn interpreter_struct_pattern_matches_renamed_same_named_structs() {
    assert_eq!(interp_run_modules(&[("qa", QA), ("qb", QB)], PATTERN_MAIN), 0);
}

#[test]
fn interpreter_overload_scores_a_renamed_class_in_its_own_module() {
    let main = "use pkg.qc.{Thing}\nuse pkg.qb.{qb_show}\n\nfn main() -> i64:\n    val t = Thing(n: 0)\n    if qb_show() != 1122:\n        return 1\n    0\n";
    assert_eq!(interp_run_modules(&[("qc", QC), ("qb", QB)], main), 0);
}

fn jit_run_modules(modules: &[(&str, &str)], main: &str) -> i64 {
    let (_dir, main_path) = write_modules(modules, main);
    interpreter::set_current_file(Some(main_path.clone()));
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
    interpreter::set_current_file(None);
    code
}

#[test]
fn jit_struct_pattern_matches_renamed_same_named_structs() {
    assert_eq!(jit_run_modules(&[("qa", QA), ("qb", QB)], PATTERN_MAIN), 0);
}

#[test]
fn interpreter_struct_pattern_rejects_the_other_modules_struct() {
    let main = "use pkg.qa.{qa_make, qa_any}\nuse pkg.qb.{qb_make}\n\nfn main() -> i64:\n    if qa_any(qa_make()) != 3:\n        return 1\n    if qa_any(qb_make()) != -1:\n        return 2\n    0\n";
    assert_eq!(interp_run_modules(&[("qa", QA), ("qb", QB)], main), 0);
}

#[test]
fn interpreter_alias_pattern_rejects_the_other_modules_struct() {
    let main = "use pkg.qa.{P, qa_make}\nuse pkg.qb.{P as Q, qb_make}\n\nfn mp(p) -> i64:\n    match p:\n        case P { x }:\n            x\n        case _:\n            -1\n\nfn mq(p) -> i64:\n    match p:\n        case Q { x }:\n            x\n        case _:\n            -1\n\nfn main() -> i64:\n    if mp(qa_make()) != 3:\n        return 1\n    if mp(qb_make()) != -1:\n        return 2\n    if mq(qa_make()) != -1:\n        return 3\n    if mq(qb_make()) != 5:\n        return 4\n    0\n";
    assert_eq!(interp_run_modules(&[("qa", QA), ("qb", QB)], main), 0);
}

/// Fable re-review t4: the entry's own bare `P` is not `qa`'s `P`.
#[test]
fn interpreter_entry_bare_struct_is_not_another_modules_struct() {
    let main = "use pkg.qa.{qa_make, qa_any}\n\nstruct P:\n    x: i64\n\nfn m_entry(p) -> i64:\n    match p:\n        case P { x }:\n            x\n        case _:\n            -1\n\nfn main() -> i64:\n    if qa_any(P(x: 9)) != -1:\n        return 1\n    if m_entry(qa_make()) != -1:\n        return 2\n    if m_entry(P(x: 9)) != 9:\n        return 3\n    0\n";
    assert_eq!(interp_run_modules(&[("qa", QA)], main), 0);
}
