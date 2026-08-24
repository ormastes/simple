// A `me`-mutating method on a CLASS receiver must cost the same however many
// parameter hops the receiver travelled to reach the mutating frame.
//
// Until 2026-08-22 it did not. `calls.rs`'s MECALL-OWNED fast path takes the
// receiver OUT of the calling frame (`env.remove`) so `self.parts.push(x)`
// mutates a uniquely-owned Arc in place. That works only when the frame doing
// `w.put(x)` is the ONLY frame holding `w`. Pass `w` one function further and
// the intermediate caller's binding keeps a live Arc on the same field for the
// whole nested call, so `Arc::make_mut` deep-copies the whole backing Vec on
// every single push — O(N^2) accumulation.
//
// Measured on 13bf3b2beee (same binary, 80,000 pushes):
//   w.put(..) called directly on a parameter :      4 clones,   0.57 s
//   passed one hop further, then w.put(..)   : 80,000 clones, 3.2e9 elements, 595 s
//
// Every generated `hc_enc_*` encoder is the second shape, which is what made
// HIR encoding quadratic (doc/08_tracking/bug/hir_codec_writer_quadratic_cow_clone_2026-08-22.md).
//
// The fix parks the caller's binding for the duration of the call (the caller
// frame is suspended and cannot observe it) and restores it from the callee's
// final value, which is exactly what `write_back_mutable_arguments` already
// does. A GENUINE alias — another live binding of the same object — still
// forces the copy-on-write clone, which the aliased control below pins.
//
// Record: doc/08_tracking/bug/seed_receiver_multi_hop_cow_clone_2026-08-22.md

use simple_compiler::interpreter;
use simple_compiler::perf_counters;
use std::collections::HashSet;
use std::fs;
use std::sync::atomic::Ordering;
use std::sync::{Mutex, OnceLock};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

// The counters are process-global, so the measuring tests must not interleave.
fn counter_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn enable_counters() {
    static ONCE: OnceLock<()> = OnceLock::new();
    ONCE.get_or_init(|| {
        std::env::set_var("SIMPLE_PERF_COUNTERS", "1");
    });
}

fn run_program(src: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, src).unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.map_err(|e| format!("{e:?}"))
}

/// `depth` extra parameter hops between the frame that owns `w` and the frame
/// that calls `w.put(..)`.
fn fixture(n: usize, depth: usize) -> String {
    let mut src = String::from(
        "class W:\n    parts: [text]\n\n    static fn create() -> W:\n        W(parts: [])\n\n    me put(v: i64):\n        self.parts.push(\"{v}\")\n\n",
    );
    src.push_str("fn h0(w: W, v: i64):\n    w.put(v)\n\n");
    for level in 1..=depth {
        src.push_str(&format!("fn h{level}(w: W, v: i64):\n    h{}(w, v)\n\n", level - 1));
    }
    let entry = if depth == 0 {
        "w.put(i)".to_string()
    } else {
        format!("h{}(w, i)", depth - 1)
    };
    src.push_str(&format!(
        "fn drive(n: i64) -> i64:\n    val w = W.create()\n    var i = 0\n    while i < n:\n        {entry}\n        i = i + 1\n    w.parts.len()\n\nfn main() -> i32:\n    if drive({n}) != {n}:\n        return 1\n    return 0\n"
    ));
    src
}

/// Elements deep-copied by the object-field array mutation path while pushing
/// `n` items through `depth` parameter hops.
fn elems_cloned(n: usize, depth: usize) -> u64 {
    enable_counters();
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let before = perf_counters::SELF_FIELD_ARR_COW_ELEMS_CLONED.load(Ordering::Relaxed);
    let result = run_program(&fixture(n, depth));
    let after = perf_counters::SELF_FIELD_ARR_COW_ELEMS_CLONED.load(Ordering::Relaxed);
    assert_eq!(result, Ok(0), "depth {depth} fixture must push exactly {n} lines");
    after - before
}

#[test]
fn me_method_field_push_is_linear_at_every_hop_depth() {
    let _guard = counter_lock().lock().unwrap_or_else(|e| e.into_inner());
    let n = 4_000usize;
    // Quadratic accumulation copies ~n^2/2 elements; linear accumulation copies
    // O(1) per push. 4n is far above any constant-factor slack and far below
    // n^2/2 (8,000 vs 8,000,000 at n = 4,000).
    let budget = (4 * n) as u64;
    let direct = elems_cloned(n, 0);
    assert!(
        direct <= budget,
        "direct receiver: {direct} elements cloned (budget {budget})"
    );
    for depth in 1..=3usize {
        let cloned = elems_cloned(n, depth);
        eprintln!("[hop] depth {depth}: {cloned} elements cloned");
        assert!(
            cloned <= budget,
            "{depth}-hop receiver deep-copied {cloned} elements for {n} pushes (budget {budget}) — \
             an intermediate frame is pinning the field Arc again"
        );
    }
}

#[test]
fn a_genuine_alias_still_forces_the_copy() {
    let _guard = counter_lock().lock().unwrap_or_else(|e| e.into_inner());
    enable_counters();
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    // `snap` is a second live binding of the same array taken BEFORE the pushes.
    // Value semantics require it to keep the old contents, which means the
    // mutation MUST clone rather than write through the shared handle.
    let n = 200usize;
    let src = format!(
        "class W:\n    parts: [text]\n\n    static fn create() -> W:\n        W(parts: [])\n\n    me put(v: i64):\n        self.parts.push(\"{{v}}\")\n\nfn h0(w: W, v: i64):\n    w.put(v)\n\nfn h1(w: W, v: i64):\n    h0(w, v)\n\nfn main() -> i32:\n    val w = W.create()\n    h1(w, 1)\n    val snap = w.parts\n    var i = 0\n    while i < {n}:\n        h1(w, i)\n        i = i + 1\n    if snap.len() != 1:\n        return 1\n    if w.parts.len() != {} :\n        return 2\n    return 0\n",
        n + 1
    );
    let before = perf_counters::SELF_FIELD_ARR_COW_ELEMS_CLONED.load(Ordering::Relaxed);
    assert_eq!(
        run_program(&src),
        Ok(0),
        "an alias taken before the pushes must not observe them"
    );
    let cloned = perf_counters::SELF_FIELD_ARR_COW_ELEMS_CLONED.load(Ordering::Relaxed) - before;
    eprintln!("[hop-alias] {cloned} elements cloned");
    assert!(
        cloned > 0,
        "a genuinely aliased field array must still copy-on-write — the park must not steal a live alias"
    );
}

#[test]
fn multi_hop_mutation_is_visible_to_the_owning_frame() {
    let _guard = counter_lock().lock().unwrap_or_else(|e| e.into_inner());
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    // Reference-class semantics: the owner sees every push made three hops down,
    // and a rebind inside the callee does not resurrect a stale binding.
    let src = "class W:\n    parts: [text]\n\n    static fn create() -> W:\n        W(parts: [])\n\n    me put(v: text):\n        self.parts.push(v)\n\nfn h0(w: W):\n    w.put(\"c\")\n\nfn h1(w: W):\n    w.put(\"b\")\n    h0(w)\n\nfn main() -> i32:\n    val w = W.create()\n    w.put(\"a\")\n    h1(w)\n    if w.parts.len() != 3:\n        return 1\n    if w.parts[0] != \"a\":\n        return 2\n    if w.parts[1] != \"b\":\n        return 3\n    if w.parts[2] != \"c\":\n        return 4\n    return 0\n";
    assert_eq!(run_program(src), Ok(0));
}
