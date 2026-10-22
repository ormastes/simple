//! Module-qualified struct identity in the flattened run/JIT lane.
//!
//! `load_module_with_imports` flattens every imported module into one unit,
//! and HIR lowering used to register struct/class types by BARE name. Two
//! modules each declaring `struct TextSpan` (different fields) therefore
//! collapsed onto one type: a function of the other module failed with
//! `Cannot infer field type: struct 'TextSpan' field 'end'` and the driver
//! dropped the WHOLE program to the interpreter (~100-1000x slower). Seen live
//! on `src/app/cli/native_build_main.spl` (frontend `block_types.TextSpan`
//! vs `db.accel.TextSpan`).
//!
//! These tests drive exactly the `run_file_jit` pipeline (load + flatten,
//! lenient HIR lowering with the project hint, MIR, Cranelift JIT) and fail if
//! any stage errors -- i.e. if the driver would have fallen back -- or if a
//! field read lands in the wrong layout (computed values are asserted).

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

const SPAN_A: &str = r#"struct TextSpan:
    start: i64
    end: i64

fn make_a() -> TextSpan:
    TextSpan(start: 1, end: 5)

fn width_a(s: TextSpan) -> i64:
    s.end - s.start
"#;

const SPAN_B: &str = r#"struct TextSpan:
    value: text
    start: i64
    len: i64

fn make_b() -> TextSpan:
    TextSpan(value: "xy", start: 7, len: 9)

fn width_b(s: TextSpan) -> i64:
    s.len
"#;

#[test]
fn same_named_structs_resolve_to_their_own_module_layout() {
    let code = jit_run_pkg(
        &[("a", SPAN_A), ("b", SPAN_B)],
        r#"use pkg.a.{make_a, width_a}
use pkg.b.{make_b, width_b}

fn main() -> i64:
    val a = make_a()
    val b = make_b()
    if width_a(a) != 4:
        return 1
    if width_b(b) != 9:
        return 2
    if a.end != 5:
        return 3
    if b.len != 9:
        return 4
    if b.start != 7:
        return 5
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn importer_annotation_and_constructor_follow_the_imported_struct() {
    // `c` imports the struct TYPE itself and constructs / annotates with it.
    let code = jit_run_pkg(
        &[
            ("a", SPAN_A),
            ("b", SPAN_B),
            (
                "c",
                r#"use pkg.b.{TextSpan}

fn c_make() -> TextSpan:
    TextSpan(value: "q", start: 2, len: 30)

fn c_len(s: TextSpan) -> i64:
    val t: TextSpan = s
    t.len + t.start
"#,
            ),
        ],
        r#"use pkg.a.{make_a, width_a}
use pkg.c.{c_make, c_len}

fn main() -> i64:
    if c_len(c_make()) != 32:
        return 1
    if width_a(make_a()) != 4:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn entry_module_struct_keeps_its_own_layout() {
    let code = jit_run_pkg(
        &[("b", SPAN_B)],
        r#"use pkg.b.{make_b, width_b}

struct TextSpan:
    start: i64
    end: i64

fn main() -> i64:
    val mine = TextSpan(start: 3, end: 10)
    if mine.end - mine.start != 7:
        return 1
    if width_b(make_b()) != 9:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn methods_and_static_calls_bind_to_the_owner_struct() {
    let code = jit_run_pkg(
        &[
            (
                "a",
                r#"struct Acc:
    v: i64
    extra: i64

impl Acc:
    static fn make(v: i64) -> Acc:
        Acc(v: v, extra: 1)
    fn total() -> i64:
        self.v + self.extra

fn a_total() -> i64:
    Acc.make(10).total()
"#,
            ),
            (
                "b",
                r#"struct Acc:
    v: i64

impl Acc:
    static fn make(v: i64) -> Acc:
        Acc(v: v)
    fn total() -> i64:
        self.v * 2

fn b_total() -> i64:
    Acc.make(21).total()
"#,
            ),
        ],
        r#"use pkg.a.{a_total}
use pkg.b.{b_total}

fn main() -> i64:
    if a_total() != 11:
        return 1
    if b_total() != 42:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn struct_and_class_with_same_name_keep_distinct_layouts() {
    let code = jit_run_pkg(
        &[
            (
                "m1",
                "struct Node:\n    left: i64\n    right: i64\n\nfn mk1() -> Node:\n    Node(left: 1, right: 2)\n",
            ),
            (
                "m2",
                "class Node:\n    tag: i64\n    weight: i64\n\nfn mk2() -> Node:\n    Node(tag: 8, weight: 9)\n",
            ),
        ],
        r#"use pkg.m1.{mk1}
use pkg.m2.{mk2}

fn main() -> i64:
    if mk1().right != 2:
        return 1
    if mk2().weight != 9:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn aliased_struct_import_resolves_to_the_named_module() {
    let code = jit_run_pkg(
        &[("a", SPAN_A), ("b", SPAN_B)],
        r#"use pkg.a.{make_a}
use pkg.b.{TextSpan as BSpan}

fn main() -> i64:
    val s = BSpan(value: "z", start: 4, len: 6)
    if s.len + s.start != 10:
        return 1
    if make_a().end != 5:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn reexported_struct_follows_the_facade_to_its_declaring_module() {
    let code = jit_run_pkg(
        &[
            ("a", SPAN_A),
            ("b", SPAN_B),
            ("facade", "export use pkg.b.{TextSpan}\n"),
        ],
        r#"use pkg.a.{make_a}
use pkg.facade.{TextSpan}

fn main() -> i64:
    val s = TextSpan(value: "r", start: 5, len: 8)
    if s.len - s.start != 3:
        return 1
    if make_a().end != 5:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn same_named_generic_structs_keep_their_own_layouts() {
    let code = jit_run_pkg(
        &[
            (
                "g1",
                "struct Cell<T>:\n    item: T\n    count: i64\n\nfn g1_count() -> i64:\n    val c: Cell<i64> = Cell(item: 4, count: 3)\n    c.count + c.item\n",
            ),
            (
                "g2",
                "struct Cell<T>:\n    weight: i64\n    item: T\n\nfn g2_weight() -> i64:\n    val c: Cell<i64> = Cell(weight: 50, item: 6)\n    c.weight + c.item\n",
            ),
        ],
        r#"use pkg.g1.{g1_count}
use pkg.g2.{g2_weight}

fn main() -> i64:
    if g1_count() != 7:
        return 1
    if g2_weight() != 56:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn enum_payload_in_non_default_owner_uses_its_own_struct_layout() {
    // `b` loads first, so `a` (loaded last) keeps the bare name and `b`'s
    // TextSpan is the renamed one: the enum payload must follow `b`.
    let code = jit_run_pkg(
        &[
            ("a", SPAN_A),
            (
                "b",
                r#"struct TextSpan:
    value: text
    start: i64
    len: i64

enum Tok:
    Word(TextSpan)
    Eof

fn b_tok() -> Tok:
    Tok.Word(TextSpan(value: "w", start: 3, len: 40))

fn b_read(t: Tok) -> i64:
    match t:
        Tok.Word(s):
            return s.len + s.start
        Tok.Eof:
            return -1
"#,
            ),
        ],
        r#"use pkg.b.{b_tok, b_read}
use pkg.a.{make_a}

fn main() -> i64:
    if b_read(b_tok()) != 43:
        return 1
    if make_a().end != 5:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn impl_block_in_importing_module_extends_the_imported_struct() {
    let code = jit_run_pkg(
        &[
            ("a", SPAN_A),
            ("b", SPAN_B),
            (
                "c",
                r#"use pkg.a.{TextSpan}

impl TextSpan:
    fn width() -> i64:
        self.end - self.start

fn c_width() -> i64:
    TextSpan(start: 2, end: 9).width()
"#,
            ),
        ],
        r#"use pkg.c.{c_width}
use pkg.b.{width_b, make_b}

fn main() -> i64:
    if c_width() != 7:
        return 1
    if width_b(make_b()) != 9:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
#[should_panic(expected = "type alias `Spanish`")]
fn type_alias_of_a_colliding_struct_fails_closed() {
    jit_run_pkg(
        &[("a", SPAN_A), ("b", SPAN_B), ("c", "use pkg.b.{TextSpan}\n\ntype Spanish = TextSpan\n\nfn c_len(s: Spanish) -> i64:\n    s.len\n")],
        "use pkg.a.{make_a}\nuse pkg.c.{c_len}\n\nfn main() -> i64:\n    make_a().end\n",
    );
}
