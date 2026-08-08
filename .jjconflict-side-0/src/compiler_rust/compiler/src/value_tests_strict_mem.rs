// M5 strict-interpreter-mode tests: "poison-on-free" / stale-state defect
// class (plan §M5, design doc §3.2 "dirty-names invariant"). Distinct from
// value_tests_basic.rs's structural tests: these are a sabotage-verified
// proof that `check_dirty_names_invariant` actually detects the exact
// violation shape the historical `copy_back_block_writes` bug produced
// (copying every shared key instead of only `dirty_names` replayed a cloned
// block env's stale snapshot over values a deeper call had since written).
//
// Deliberately does NOT call `value::strict_mem_enable()` anywhere in this
// file: that flag is a process-global, once-set-never-unset `AtomicBool`
// (see `value.rs` `STRICT_MEM_FORCED`), and this file is `include!`-d into
// the crate's single shared `--lib` unit-test binary alongside many other
// `#[cfg(test)]` modules that exercise the interpreter — flipping it here
// would leak into every other test in that binary, in an order cargo does
// not guarantee (`tests/interpreter_strict_mem_test.rs` documents the same
// hazard and isolates itself in its own integration-test binary/process
// instead). `assert_dirty_names_invariant` was split out of
// `copy_back_block_writes` specifically so its panic behavior can be
// exercised directly, gate-free, without touching `STRICT_MEM_FORCED`.
use super::*;

#[test]
fn dirty_names_invariant_holds_after_a_real_write() {
    // Normal path: `insert()` writes into both `overlay` and `dirty_names`
    // together, so the invariant holds and the check finds nothing.
    let mut env = CowEnv::new();
    env.insert("x".to_string(), Value::Int(1));
    assert_eq!(env.check_dirty_names_invariant(), None);
}

#[test]
fn dirty_names_invariant_holds_on_a_fresh_env() {
    let env = CowEnv::new();
    assert_eq!(env.check_dirty_names_invariant(), None);
}

#[test]
fn dirty_names_invariant_catches_the_historical_violation_shape() {
    // Sabotage: force exactly the state the pre-fix `copy_back_block_writes`
    // bug could produce -- a name recorded dirty with no corresponding
    // overlay entry (e.g. present only via a stale clone). Baseline (no
    // sabotage, tested above) returns None; this is the RED case.
    let mut env = CowEnv::new();
    env.test_mark_dirty_without_overlay("stale_name");
    assert_eq!(
        env.check_dirty_names_invariant(),
        Some("stale_name"),
        "the invariant check must name the offending key so the trap is attributable"
    );
}

#[test]
fn dirty_names_invariant_ignores_a_correctly_written_name_alongside_a_bad_one() {
    // The check must find the FIRST violator without being confused by
    // otherwise-correct dirty entries in the same env.
    let mut env = CowEnv::new();
    env.insert("good".to_string(), Value::Int(1));
    env.test_mark_dirty_without_overlay("stale_name");
    let offender = env.check_dirty_names_invariant();
    assert!(offender == Some("stale_name"), "got {offender:?}");
}

#[test]
#[should_panic(expected = "strict-mem: dirty-names invariant violated")]
fn assert_dirty_names_invariant_traps_on_violation() {
    // End-to-end proof at the real call site's logic (the panic message and
    // trigger condition `copy_back_block_writes` gates on `strict_mem_enabled()`
    // before calling), without forcing the process-global strict-mode flag.
    let mut env = CowEnv::new();
    env.test_mark_dirty_without_overlay("stale_name");
    crate::interpreter::assert_dirty_names_invariant(&env);
}

#[test]
fn assert_dirty_names_invariant_is_silent_when_invariant_holds() {
    // Negative control: the same call, on a correctly-written env, must not
    // panic -- proves the trap fires on the violation, not unconditionally.
    let mut env = CowEnv::new();
    env.insert("x".to_string(), Value::Int(1));
    crate::interpreter::assert_dirty_names_invariant(&env);
}
