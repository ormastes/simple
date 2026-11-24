//! JIT codegen runs Cranelift's per-function compile on worker threads.
//!
//! After reachability pruning the web renderer still JIT-compiles ~4,300
//! functions, and Cranelift codegen (`Context::compile`: lowering, regalloc,
//! emission) was ~2.1 s of tab-bar's 5.5 s wall, all on one thread, while the
//! interpreter finished the page in 4.8 s. Codegen needs only the ISA, so the
//! JIT translates on the calling thread and compiles on
//! `SIMPLE_JIT_CODEGEN_THREADS` workers, defining in submission order.
//! Bug: doc/08_tracking/bug/jit_serial_cranelift_codegen_startup_2026-11-24.md
//!
//! One test in this binary: it sets `SIMPLE_JIT_CODEGEN_THREADS`, which the JIT
//! reads at construction, so no other test may run concurrently with it.

use std::time::Instant;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

const FUNCS: usize = 120;
const ARMS: usize = 40;

/// `FUNCS` functions of `ARMS` if-expressions each; `main` sums them all.
/// (Named `g<n>`: a user `fn f32` call JITs as the `f32` cast — see the bug record.)
fn source() -> String {
    let mut s = String::new();
    for f in 0..FUNCS {
        s.push_str(&format!("fn g{f}(x: i64) -> i64:\n    var s = {f}\n"));
        for i in 0..ARMS {
            s.push_str(&format!("    s = s + (if x > {i}: x * {i} else: {i} - x + {f})\n"));
        }
        s.push_str("    s\n\n");
    }
    s.push_str("fn main() -> i64:\n    var t = 0\n");
    for f in 0..FUNCS {
        s.push_str(&format!("    t = t + g{f}(17)\n"));
    }
    s.push_str("    t\n");
    s
}

fn expected(x: i64) -> i64 {
    (0..FUNCS as i64)
        .map(|f| f + (0..ARMS as i64).map(|i| if x > i { x * i } else { i - x + f }).sum::<i64>())
        .sum()
}

/// (main's result, seconds in `compile_module`) with `threads` codegen workers.
fn compile_and_run(mir_module: &mir::MirModule, threads: &str) -> (i64, f64) {
    std::env::set_var("SIMPLE_JIT_CODEGEN_THREADS", threads);
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    let start = Instant::now();
    jit.compile_module(mir_module).expect("module must JIT-compile");
    let secs = start.elapsed().as_secs_f64();
    let v = unsafe { jit.call_i64_void("main").expect("main must execute") };
    (v, secs)
}

#[test]
fn codegen_workers_cut_compile_time_and_keep_results() {
    let src = source();
    let ast = Parser::new(&src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let _ = compile_and_run(&mir_module, "1"); // warm-up
    // Fastest of three, alternating order: one scheduler stall must not decide.
    let (mut serial, mut parallel) = (f64::INFINITY, f64::INFINITY);
    for _ in 0..3 {
        let (v1, t1) = compile_and_run(&mir_module, "1");
        let (v4, t4) = compile_and_run(&mir_module, "4");
        assert_eq!(v1, expected(17));
        assert_eq!(v4, expected(17));
        serial = serial.min(t1);
        parallel = parallel.min(t4);
    }
    std::env::remove_var("SIMPLE_JIT_CODEGEN_THREADS");
    // Serial codegen: ratio ~1. Four workers with translation still serial
    // measured well under 0.8 (see the bug record for the numbers).
    let ratio = parallel / serial;
    eprintln!("codegen serial {serial:.3}s, 4 workers {parallel:.3}s, ratio {ratio:.2}");
    // Four workers cannot beat serial on fewer than four cores; the values
    // above are still checked there.
    if std::thread::available_parallelism().map_or(1, |n| n.get()) < 4 {
        return;
    }
    assert!(
        ratio < 0.8,
        "4 codegen workers did not speed up compile: serial {serial:.3}s, parallel {parallel:.3}s, ratio {ratio:.2}"
    );
}
