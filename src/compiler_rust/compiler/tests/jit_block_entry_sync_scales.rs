//! JIT codegen: block-entry variable sync must not be O(vars x blocks).
//!
//! `compile_function_body` re-read EVERY cross-block vreg (`use_var`) at the
//! entry of EVERY block, and every block is sealed only at the end of the
//! function. On an unsealed block each `use_var` adds a block parameter, so a
//! function with many short-lived temporaries paid vars x blocks: the web
//! renderer's `layout_with_style_flow` (2,212 vars x 3,134 blocks) and
//! `_apply_decls_without_grid_inner` took ~1 s each to translate, and the
//! catalog spent ~9.5 s in `compile_all` per run. Only the block's live-in
//! vregs need a fresh value at its entry.
//! Bug: doc/08_tracking/bug/jit_block_entry_sync_all_vars_quadratic_compile_2026-11-23.md

use std::time::Instant;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

/// `n` if-expressions: each one merges its arms through a short-lived
/// cross-block vreg (the shape of the renderer's long style/layout functions).
fn source(n: usize) -> String {
    let mut s = String::from("fn big(x: i64) -> i64:\n    var s = 0\n");
    for i in 0..n {
        s.push_str(&format!("    s = s + (if x > {i}: x * {i} else: {i} - x)\n"));
    }
    s.push_str("    s\n\nfn main() -> i64:\n    big(7)\n");
    s
}

fn expected(n: usize, x: i64) -> i64 {
    (0..n as i64).map(|i| if x > i { x * i } else { i - x }).sum()
}

/// (main's result, seconds spent in `compile_module`).
fn compile_and_run(n: usize) -> (i64, f64) {
    let src = source(n);
    let ast = Parser::new(&src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    let start = Instant::now();
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let secs = start.elapsed().as_secs_f64();
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    (v, secs)
}

#[test]
fn many_short_lived_temporaries_compile_in_linear_time() {
    let n = 300;
    // Warm-up: first JIT construction pays one-off setup.
    let _ = compile_and_run(20);
    // Fastest of three per size: a scheduler stall on one run must not decide.
    let best = |size: usize| {
        let runs: Vec<(i64, f64)> = (0..3).map(|_| compile_and_run(size)).collect();
        let t = runs.iter().map(|r| r.1).fold(f64::INFINITY, f64::min);
        (runs[0].0, t)
    };
    let (v1, t1) = best(n);
    let (v2, t2) = best(2 * n);
    assert_eq!(v1, expected(n, 7));
    assert_eq!(v2, expected(2 * n, 7));
    // vars x blocks translation measured ratio 6-7 here; live-in sync measured
    // ~3.2 (Cranelift's own register allocation is mildly superlinear too).
    let ratio = t2 / t1;
    assert!(ratio < 5.0, "compile time grows superlinearly: n={n} {t1:.3}s, 2n {t2:.3}s, ratio {ratio:.2}");
}

#[test]
fn temporaries_live_across_loops_keep_their_values() {
    // A loop header is entered from before the loop and from its latch; only
    // vregs live into it may be re-read there. Values must survive both edges.
    let src = "fn f(n: i64) -> i64:
    val a = n * 3
    var i = 0
    var acc = 0
    while i < n:
        val b = i + a
        if b % 2 == 0:
            acc = acc + b
        else:
            acc = acc - 1
        i = i + 1
    acc + a

fn main() -> i64:
    f(10)
";
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    let a = 30;
    let want: i64 = (0..10).map(|i| if (i + a) % 2 == 0 { i + a } else { -1 }).sum::<i64>() + a;
    assert_eq!(v, want);
}
