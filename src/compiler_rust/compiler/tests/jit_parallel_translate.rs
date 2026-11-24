//! JIT MIR->CLIF translation runs on worker threads, and the code it defines
//! is byte-identical to the serial loop.
//!
//! After parallel codegen (`jit_parallel_codegen.rs`) the serial translation
//! loop was the JIT's critical path: ~720 ms of tab-bar's ~3.0 s. Workers now
//! translate against a frozen snapshot of the declarations and `func_ids`; the
//! calling thread replays each function's new declarations in the original
//! order, so FuncIds/DataIds, CLIF and machine code match the serial loop.
//! Bug: doc/08_tracking/bug/jit_serial_cranelift_codegen_startup_2026-11-24.md
//!
//! One test in this binary: it sets `SIMPLE_JIT_CODEGEN_THREADS` and
//! `SIMPLE_JIT_XLATE_STALE_EVERY`, which the JIT reads at construction / per
//! module, so no other test may run concurrently with it.

use simple_compiler::codegen::common_backend::{BodyLoopStats, CapturedFunction};
use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

const FUNCS: usize = 160;
const ARMS: usize = 24;

/// Functions that mix shared and unique string literals (content-named data
/// objects declared during translation), array pushes (runtime imports),
/// struct methods and erased-receiver method calls (the `func_ids` suffix
/// scan), so the declare-on-demand paths run, not only arithmetic.
fn source() -> String {
    let mut s = String::new();
    // A trait implemented by every struct: calls through a trait-typed
    // parameter take the vtable-slot path, whose JIT receiver guard is keyed
    // on the module type (workers translate through a stand-in module).
    s.push_str("trait Scored:\n    fn scored() -> i64\n\n");
    for b in 0..4 {
        s.push_str(&format!(
            "struct Cell{b}:\n    var seed: i64\n\n    fn pick{b}(k: i64) -> i64:\n        return me.seed + k + {b}\n\n"
        ));
        s.push_str(&format!("impl Scored for Cell{b}:\n    fn scored() -> i64:\n        return me.seed * 2\n\n"));
        s.push_str(&format!("fn make{b}(x: i64) -> Cell{b}:\n    return Cell{b}(x)\n\n"));
    }
    s.push_str("fn via_trait(v: Scored) -> i64:\n    return v.scored()\n\n");
    for f in 0..FUNCS {
        let b = f % 4;
        s.push_str(&format!("fn g{f}(x: i64) -> i64:\n    var s = {f}\n"));
        s.push_str(&format!("    val t = \"item-{}\"\n", f % 7));
        s.push_str(&format!("    val u = \"unique-{f}-text\"\n"));
        s.push_str("    s = s + t.len() + u.len()\n");
        s.push_str("    var a: [i64] = []\n    a.push(x)\n");
        s.push_str(&format!("    a.push({f})\n    s = s + a.len()\n"));
        s.push_str(&format!("    val c = make{b}(x)\n    s = s + c.pick{b}({f})\n"));
        if f % 5 == 0 {
            s.push_str(&format!("    var e: Any = make{b}(x)\n    s = s + e.pick{b}(1)\n"));
        }
        if f % 6 == 0 {
            s.push_str(&format!("    s = s + via_trait(make{b}(x))\n"));
        }
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
        .map(|f| {
            let b = f % 4;
            let mut s = f;
            s += 6 + format!("unique-{f}-text").len() as i64;
            s += 2;
            s += x + f + b;
            if f % 5 == 0 {
                s += x + 1 + b;
            }
            if f % 6 == 0 {
                s += 2 * x;
            }
            s + (0..ARMS as i64).map(|i| if x > i { x * i } else { i - x + f }).sum::<i64>()
        })
        .sum()
}

struct Run {
    value: i64,
    stats: BodyLoopStats,
    code: Vec<CapturedFunction>,
}

fn compile_and_run(mir_module: &mir::MirModule, threads: &str, stale_every: &str) -> Run {
    std::env::set_var("SIMPLE_JIT_CODEGEN_THREADS", threads);
    std::env::set_var("SIMPLE_JIT_XLATE_STALE_EVERY", stale_every);
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.capture_compiled_code();
    jit.compile_module(mir_module).expect("module must JIT-compile");
    let value = unsafe { jit.call_i64_void("main").expect("main must execute") };
    Run { value, stats: jit.body_loop_stats(), code: jit.take_captured_code() }
}

fn assert_same_code(serial: &[CapturedFunction], other: &[CapturedFunction], what: &str) {
    assert_eq!(serial.len(), other.len(), "{what}: defined body count differs");
    for (a, b) in serial.iter().zip(other) {
        assert_eq!(a.name, b.name, "{what}: define order differs");
        assert_eq!(a.clif, b.clif, "{what}: CLIF of {} differs", a.name);
        assert_eq!(a.code, b.code, "{what}: machine code of {} differs", a.name);
    }
}

#[test]
fn translation_runs_on_workers_and_matches_serial_code() {
    let src = source();
    let ast = Parser::new(&src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let _ = compile_and_run(&mir_module, "1", "0"); // warm-up

    let serial = compile_and_run(&mir_module, "1", "0");
    assert_eq!(serial.value, expected(17));
    assert!(serial.code.len() > FUNCS, "capture must see every body");

    // Best of three, alternating: one scheduler stall must not decide.
    let (mut serial_ns, mut parallel_ns) = (u64::MAX, u64::MAX);
    let mut parallel_stats = BodyLoopStats::default();
    for _ in 0..3 {
        let p = compile_and_run(&mir_module, "8", "0");
        let s = compile_and_run(&mir_module, "1", "0");
        assert_eq!(p.value, expected(17));
        assert_eq!(s.value, expected(17));
        assert_same_code(&serial.code, &p.code, "8 workers");
        assert_same_code(&serial.code, &s.code, "serial rerun");
        serial_ns = serial_ns.min(s.stats.main_translate_ns);
        if p.stats.main_translate_ns < parallel_ns {
            parallel_ns = p.stats.main_translate_ns;
            parallel_stats = p.stats;
        }
    }

    // Forced staleness: every 3rd worker translation is discarded and redone
    // on the calling thread. The defined code must not change.
    let forced = compile_and_run(&mir_module, "8", "3");
    std::env::remove_var("SIMPLE_JIT_CODEGEN_THREADS");
    std::env::remove_var("SIMPLE_JIT_XLATE_STALE_EVERY");
    assert_eq!(forced.value, expected(17));
    assert_same_code(&serial.code, &forced.code, "forced stale");

    let ratio = parallel_ns as f64 / serial_ns as f64;
    eprintln!(
        "main-thread translate: serial {:.1} ms, 8 workers {:.1} ms, ratio {ratio:.2}; parallel {:?}; forced {:?}",
        serial_ns as f64 / 1e6,
        parallel_ns as f64 / 1e6,
        parallel_stats,
        forced.stats
    );
    assert!(parallel_stats.worker_translated > 0, "no body was translated on a worker: {parallel_stats:?}");
    assert!(forced.stats.stale > 0, "forced staleness never fired: {:?}", forced.stats);
    // With translation on the calling thread the ratio is ~1.0. Workers leave
    // it only the stale re-translations.
    assert!(
        ratio < 0.35,
        "translation still runs on the calling thread: serial {serial_ns} ns, parallel {parallel_ns} ns, ratio {ratio:.2}"
    );
}
