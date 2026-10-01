//! Regression guard for the seed interpreter's execution-phase memory.
//!
//! `doc/08_tracking/bug/native_build_worker_interpreter_heap_grows_unbounded_2026-08-17.md`
//! reported that RSS grows without bound while an interpreted program runs, and
//! attributed it to the runtime value heap's registry
//! (`runtime/src/value/heap.rs`), which frees nothing without an explicit
//! destructor call. Direct measurement on 2026-09-06 refuted that attribution
//! for the INTERPRETER lane on both counts, and this test pins both halves so
//! either can regress loudly:
//!
//! 1. Interpreted values are Rust `Value`s (`Arc`/`Vec`/`String`), so they never
//!    enter `HEAP_ALLOCATION_REGISTRY` at all. A whole-compiler-graph run
//!    registered 374 objects / 13 KB against 3.25 GB RSS.
//! 2. Those Rust values ARE reclaimed when they go out of scope, so per-iteration
//!    heap churn does not accumulate: running the same allocating loop ten times
//!    longer does not retain ten times more.
//!
//! The compiled/JIT lane is a different story and is deliberately NOT covered
//! here — there the registry leak is real and unbounded (`rt_frees == 0` after
//! 110 million allocations). See the bug record.
//!
//! This test binary installs its own tracking allocator because `TrackingAlloc`
//! is declared in `driver/src/main.rs` (the bin), not in the library, so
//! `mem_trace::live()` reads zero in any test binary that does not install one.
//! `rss_bytes()` is not a substitute: allocator slack makes it far too noisy to
//! band at this resolution.

use std::alloc::System;

use simple_compiler::mem_trace::{self, TrackingAlloc};
use simple_driver::interpreter::run_code;

#[global_allocator]
static GLOBAL: TrackingAlloc<System> = TrackingAlloc::new(System);

/// Work per iteration: build a 40-element array of freshly allocated strings and
/// a 40-entry dict, then drop both. The live working set is O(1) in `iters`, so
/// retained bytes must be too.
const ELEMENTS_PER_ITERATION: i64 = 40;

/// An allocating loop whose live working set is O(1) in `iters`.
///
/// Written with untyped `fn` parameters and the `main = <expr>` form on purpose:
/// the `fn main() -> i64:` form with typed parameters SIGBUSes inside `run_code`
/// on this host (a separate defect, noted in the bug record — not exercised
/// here, because this test must fail on memory growth and nothing else).
fn churn_program(iters: i64) -> String {
    format!(
        r#"
fn build(n):
    var a = []
    var i = 0
    while i < n:
        a.push("item-" + i.to_text())
        i = i + 1
    var d = {{}}
    var j = 0
    while j < n:
        d["k" + j.to_text()] = a[j]
        j = j + 1
    a.len() + d.len()

fn run(iters):
    var total = 0
    var r = 0
    while r < iters:
        total = total + build({elements})
        r = r + 1
    total

main = run({iters}) - run({iters})
"#,
        elements = ELEMENTS_PER_ITERATION
    )
}

/// Run the program and report `(peak growth during the run, bytes still live
/// after it)`.
///
/// The peak delta is the load-bearing one: the reported defect is RSS climbing
/// *while* the program executes, and a program-local leak is invisible to a
/// post-run `live()` reading because the interpreter's own structures are
/// dropped when `run_code` returns.
fn run_and_measure(iters: i64) -> (usize, usize) {
    let peak_before = mem_trace::peak();
    let live_before = mem_trace::live();
    let result = run_code(&churn_program(iters), &[], "").expect("churn program must run");
    assert_eq!(result.exit_code, 0, "churn program must exit 0");
    (
        mem_trace::peak().saturating_sub(peak_before),
        mem_trace::live().saturating_sub(live_before),
    )
}

#[test]
fn interpreted_value_churn_does_not_accumulate() {
    // The interpreter recurses deeply enough to blow the 2 MB stack a `#[test]`
    // thread gets (it dies with SIGBUS, not a Rust panic, so the failure is
    // opaque). `driver/src/main.rs` spawns a 64 MB stack for the same reason.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(churn_does_not_accumulate)
        .expect("spawn interpreter thread")
        .join()
        .expect("interpreter thread panicked");
}

fn churn_does_not_accumulate() {
    const SMALL_ITERS: i64 = 500;
    const LARGE_ITERS: i64 = 5_000; // 10x the work, same live working set

    // Warm-up at the SMALL size: this run pays the process-lifetime startup
    // cost (prelude, module tables, string interner) and sets the high-water
    // mark for one pass of the loop. Everything after it is measured against
    // that mark, so only growth that scales with iteration count can register.
    let (warmup_peak, warmup_live) = run_and_measure(SMALL_ITERS);

    let (large_peak, large_live) = run_and_measure(LARGE_ITERS);
    let registered = registered_runtime_heap_objects();

    eprintln!(
        "[heap-reclaim] warmup({SMALL_ITERS} iters) peak+{warmup_peak}B live+{warmup_live}B; \
         large({LARGE_ITERS} iters) peak+{large_peak}B live+{large_live}B; rt_registry={registered}"
    );

    // The large run does 10x the work of the warm-up with the same live working
    // set (one 40-element array and dict at a time). If interpreted values were
    // never reclaimed it would hold all 5_000 * 40 * 2 = 400_000 container
    // elements plus their strings at once, pushing the high-water mark tens of
    // MB above the warm-up's. Bounded execution adds essentially nothing.
    const PEAK_BUDGET: usize = 4 * 1024 * 1024;
    assert!(
        large_peak <= PEAK_BUDGET,
        "interpreted execution grew with iteration count: {LARGE_ITERS} iterations \
         raised the allocator high-water mark by {large_peak} bytes over a \
         {SMALL_ITERS}-iteration warm-up (budget {PEAK_BUDGET}). The seed \
         interpreter is retaining per-iteration values; see \
         doc/08_tracking/bug/native_build_worker_interpreter_heap_grows_unbounded_2026-08-17.md"
    );

    // Nothing from the loop may outlive the run either.
    const LIVE_BUDGET: usize = 4 * 1024 * 1024;
    assert!(
        large_live <= LIVE_BUDGET,
        "interpreted execution leaked past the run: {LARGE_ITERS} iterations left \
         {large_live} bytes live (budget {LIVE_BUDGET})"
    );

    // The runtime value heap is not on the interpreter's allocation path at all.
    // This bound is deliberately loose (an SFFI call may box a value); the
    // measured figure for a whole-compiler-graph run is 374, and for the
    // compiled lane running this same program it is over 100 million.
    assert!(
        registered < 10_000,
        "interpreted execution registered {registered} runtime-heap objects; the \
         interpreter lane is expected to stay off the rt_* value heap, so either \
         the interpreter now allocates through it (re-measure the registry's \
         contribution to RSS) or the bug record's original attribution has \
         become true"
    );
}

fn registered_runtime_heap_objects() -> i64 {
    extern "C" {
        fn rt_heap_registry_count() -> i64;
    }
    unsafe { rt_heap_registry_count() }
}
