//! Cranelift JIT (`lower_to_mir_jit`): verify overwritten string locals,
//! interpolated f-strings (`rt_string_concat`/`rt_value_to_string`), `print`
//! temporaries, and self-append + return loops (`cs_live_paint`) reclaim old
//! `RuntimeString` buffers immediately instead of leaking unboundedly.
//! Bug: doc/08_tracking/bug/caret_cs_jit_lane_never_frees_rss_growth_2026-11-14.md

use std::sync::Mutex;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use simple_runtime::value::heap::{rt_heap_live_bytes_by_kind, rt_heap_live_count_by_kind};
use simple_runtime::value::HeapObjectType;

static HEAP_MEASURE_LOCK: Mutex<()> = Mutex::new(());

fn run_jit(src: &str) -> (i64, i64, i64, usize) {
    let _guard = HEAP_MEASURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    simple_runtime::register_static_runtime_symbols();
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir_jit(&hir_module).expect("source must JIT-lower to MIR");
    let drops = mir_module
        .functions
        .iter()
        .map(|f| {
            f.blocks
                .iter()
                .flat_map(|b| &b.instructions)
                .filter(|inst| matches!(inst, mir::MirInst::Drop { .. }))
                .count()
        })
        .sum();
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let kind = HeapObjectType::String as i64;
    let before_count = rt_heap_live_count_by_kind(kind);
    let before_bytes = rt_heap_live_bytes_by_kind(kind);
    let result = unsafe { jit.call_i64_void("main").expect("main must execute") };
    let delta_count = rt_heap_live_count_by_kind(kind) - before_count;
    let delta_bytes = rt_heap_live_bytes_by_kind(kind) - before_bytes;
    (result, delta_count, delta_bytes, drops)
}

#[test]
fn minimal_string_overwrite_with_concat_use_stays_flat() {
    // Exact minimal repro shape from the bug report:
    // `keep = "x" + i.to_text()` inside a loop, consumed afterwards inside
    // string concatenation `"end rss " + ... + keep`.
    let make_src = |iters: usize| {
        format!(
            r#"
fn main() -> i64:
    var keep = ""
    var i = 0
    while i < {iters}:
        keep = "x" + i.to_text()
        i = i + 1
    val summary = "end " + keep
    if summary != "end x{}":
        return 1
    if keep != "x{}":
        return 2
    summary.len()
"#,
            iters - 1,
            iters - 1
        )
    };
    let (res_small, small_count, _small_bytes, _) = run_jit(&make_src(50));
    let (res, delta_count, delta_bytes, drops) = run_jit(&make_src(5000));
    assert_eq!(res_small, 7);
    assert_eq!(res, 9);
    assert!(drops >= 2, "expected string Drop instructions in MIR, got {drops}");
    assert!(
        delta_count <= 8 && delta_count <= small_count + 2,
        "overwritten string loop scaled with iterations: small_count={small_count}, delta_count={delta_count}, delta_bytes={delta_bytes}"
    );
    assert!(
        delta_bytes <= 512,
        "overwritten string loop leaked bytes: delta_bytes={delta_bytes}"
    );
}

#[test]
fn interpolated_fstring_and_print_temps_in_loop_stay_flat() {
    let src = r#"
fn main() -> i64:
    var keep = ""
    var i = 0
    var acc = 0
    while i < 2000:
        keep = "tick_{i}_{i + 1}"
        if keep.starts_with("tick_"):
            acc = acc + 1
        i = i + 1
    if !keep.contains("1999_2000"):
        return -1
    acc
"#;
    let (res, delta_count, delta_bytes, drops) = run_jit(src);
    assert_eq!(res, 2000);
    assert!(drops >= 2, "expected f-string operand/overwrite drops, got {drops}");
    assert!(
        delta_count <= 4,
        "fstring loop leaked RuntimeStrings: delta_count={delta_count}, delta_bytes={delta_bytes}"
    );
}

#[test]
fn self_append_loop_and_returns_stay_flat() {
    // Models `cs_live_paint`: `body = body + ...` across many steps inside a
    // helper that returns `body` (both explicit `return` and tail expr).
    let src = r#"
fn paint_explicit(n: i64) -> text:
    var body = ""
    var i = 0
    while i < n:
        body = body + "r" + (i % 10).to_text() + ";"
        i = i + 1
    return body

fn paint_tail(n: i64) -> text:
    var body = ""
    var i = 0
    while i < n:
        body = body + "t" + (i % 10).to_text() + ";"
        i = i + 1
    body

fn main() -> i64:
    val a = paint_explicit(1200)
    val b = paint_tail(1200)
    if !a.starts_with("r0;r1;") or !a.ends_with("r9;"):
        return -1
    if !b.starts_with("t0;t1;") or !b.ends_with("t9;"):
        return -2
    a.len() + b.len()
"#;
    let (res, delta_count, _delta_bytes, drops) = run_jit(src);
    assert_eq!(res, 1200 * 3 * 2);
    assert!(drops >= 4, "expected self-append drops, got {drops}");
    // 1200 iterations x 2 functions would allocate >7000 intermediate strings if leaked.
    assert!(
        delta_count <= 8,
        "self-append builder leaked intermediate buffers: delta_count={delta_count}"
    );
}

#[test]
fn block_scoped_fresh_strings_and_print_temps_stay_flat() {
    let src = r#"
fn main() -> i64:
    var i = 0
    var total = 0
    while i < 2000:
        val line = "item_" + i.to_text()
        if line.contains("item_"):
            val tagged = line + "!"
            total = total + tagged.len()
        if i < 200:
            println("frame_" + i.to_text())
        i = i + 1
    total
"#;
    let (res, delta_count, _delta_bytes, drops) = run_jit(src);
    assert!(res > 0);
    assert!(drops >= 3, "expected block-scoped and print string drops, got {drops}");
    assert!(
        delta_count <= 4,
        "block-scoped string loop leaked RuntimeStrings: delta_count={delta_count}"
    );
}

#[test]
fn aliased_and_defer_string_locals_keep_valid_values() {
    let src = r#"
fn keep_with_defer() -> text:
    var d = "start"
    var res = "none"
    defer:
        res = d + "_end"
    d = "mid_" + 1.to_text()
    return d

fn main() -> i64:
    var keep = ""
    var saved = ""
    var i = 0
    while i < 40:
        keep = "v" + i.to_text()
        if i == 10:
            saved = keep
        i = i + 1
    if saved != "v10" or keep != "v39":
        return 1
    if keep_with_defer() != "mid_1":
        return 2
    0
"#;
    let (res, _, _, _) = run_jit(src);
    assert_eq!(res, 0);
}
