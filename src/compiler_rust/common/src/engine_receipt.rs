//! Non-forgeable engine receipt.
//!
//! # Why this exists
//!
//! Until this module landed, a Simple program run under
//! `SIMPLE_EXECUTION_MODE=jit` and the same program run under
//! `SIMPLE_EXECUTION_MODE=interpret` produced byte-identical output, and there
//! was no way to tell whether the JIT had actually executed anything. One
//! unsupported construct silently demotes the WHOLE program to the tree-walk
//! interpreter (`exec_core.rs` `interpreter_preference_reason`, the
//! `run_file_jit` bail-outs, the `catch_unwind` fallback), and `SIMPLE_NO_JIT`
//! is a decoy with no reader in this tree at all. So every claim of the form
//! "this behaves the same on both engines" was unfalsifiable — see
//! `doc/01_research/compiler/dual_impl_test_sharing_assessment_2026-08-23.md`,
//! which measured `39 examples, 0 failures` on both lanes and had to label the
//! result unusable for exactly this reason.
//!
//! # The contract
//!
//! * The engine field is stamped by code running **inside the engine that
//!   actually executes** (the tree-walk `evaluate_module`, the JIT's
//!   `execute`), never by the CLI layer that *requested* a lane. That is the
//!   whole point: it reports what RAN, not what was asked for, so a silent
//!   demotion cannot be laundered into a green "jit" claim.
//! * No flag can set the engine field. There is no env var, no CLI option, and
//!   no public setter that takes an engine name from outside — [`stamp`] is
//!   callable only with the fixed [`Engine`] constants compiled into each
//!   engine's own execution path.
//! * A demotion is recorded whether or not a receipt was requested, and the
//!   receipt cannot be printed without its `demoted=`/`reason=` fields. When
//!   the operator EXPLICITLY asked for a compiled lane, a demotion is
//!   additionally announced on stderr unconditionally: that is the case where
//!   silence would make a false claim, and there is deliberately no knob that
//!   turns it off.
//! * Cheap when off: one `var_os` miss at the end of a run, plus one atomic
//!   store per engine entry.

use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Mutex, OnceLock};

/// The engine that actually executed the program.
///
/// Deliberately a closed set of constants rather than a string: an engine name
/// must not be constructible from user input, otherwise a flag could forge one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Engine {
    /// The Rust seed's tree-walk interpreter.
    Interpreter,
    /// The Cranelift JIT.
    CraneliftJit,
    /// The LLVM JIT.
    LlvmJit,
    /// A pre-compiled native module loaded and executed in-process.
    Native,
    /// A WebAssembly module executed under the WASI host.
    Wasm,
}

impl Engine {
    /// The stable, machine-readable spelling used in the receipt line.
    pub fn as_str(self) -> &'static str {
        match self {
            Engine::Interpreter => "interpreter",
            Engine::CraneliftJit => "cranelift-jit",
            Engine::LlvmJit => "llvm-jit",
            Engine::Native => "native",
            Engine::Wasm => "wasm",
        }
    }

    fn from_code(code: u8) -> Option<Engine> {
        match code {
            1 => Some(Engine::Interpreter),
            2 => Some(Engine::CraneliftJit),
            3 => Some(Engine::LlvmJit),
            4 => Some(Engine::Native),
            5 => Some(Engine::Wasm),
            _ => None,
        }
    }

    fn code(self) -> u8 {
        match self {
            Engine::Interpreter => 1,
            Engine::CraneliftJit => 2,
            Engine::LlvmJit => 3,
            Engine::Native => 4,
            Engine::Wasm => 5,
        }
    }
}

/// Engine actually entered. `0` = nothing has executed yet.
///
/// Last writer wins on purpose: when a lane demotes, the interpreter stamps
/// itself *after* the JIT lane gave up, so the final value is the engine that
/// really ran the program.
static ENGINE: AtomicU8 = AtomicU8::new(0);

/// Demotion reasons, in the order they occurred.
fn demotions() -> &'static Mutex<Vec<String>> {
    static DEMOTIONS: OnceLock<Mutex<Vec<String>>> = OnceLock::new();
    DEMOTIONS.get_or_init(|| Mutex::new(Vec::new()))
}

/// Record that `engine` is now executing user code.
///
/// Called from inside each engine's own execution entry point. This is the only
/// way the engine field is ever set.
pub fn stamp(engine: Engine) {
    ENGINE.store(engine.code(), Ordering::SeqCst);
}

/// The engine that actually executed, if anything did.
pub fn engine() -> Option<Engine> {
    Engine::from_code(ENGINE.load(Ordering::SeqCst))
}

/// The lane the operator asked for, or `None` when they said nothing.
fn requested_mode() -> Option<String> {
    std::env::var("SIMPLE_EXECUTION_MODE").ok()
}

/// Would this run have executed compiled code, absent a demotion?
///
/// Note the UNSET case is `true`, not `false`, and that is deliberate. The
/// seed's default lane is already the JIT (`ExecCore::with_gc_and_provider`
/// falls through to `ExecutionMode::Jit`), so "no explicit request" is a
/// request for the JIT — and it is the lane almost every real run takes. An
/// earlier draft scoped the announcement to an *explicit* request, on the
/// reasoning that only an explicit claim can be betrayed. That was wrong in the
/// direction that matters: it would have left the single most common demotion
/// path — a default-lane run silently dropping to the interpreter — exactly as
/// quiet as it was before, which is the defect.
///
/// Only an explicit *interpreter* (or wasm) request makes this false, and in
/// that case there is nothing to announce: the interpreter is what was asked
/// for. In particular the test runner forces `SIMPLE_EXECUTION_MODE=interpret`
/// on its `run` children, so the suite gains no new stderr output from this.
fn requested_a_compiled_lane() -> bool {
    match requested_mode().as_deref() {
        None => true,
        Some("interpret" | "interpreter" | "interpret-optimized") => false,
        Some("wasm" | "wasm32" | "wasi" | "wasm32-wasi") => false,
        Some(_) => true,
    }
}

/// Record a demotion away from the requested lane.
///
/// `reason` is a short stable token (`shs-extension`, `jit-compile-error`,
/// `jit-bail:generator`, ...); `detail` is free text and may be empty.
///
/// This is never silently suppressible. When a compiled lane was explicitly
/// requested the demotion is announced on stderr immediately, with no env var
/// that disables it — a demotion that happens must be visible, which is the
/// defect this module exists to fix.
pub fn record_demotion(reason: &str, detail: &str) {
    let entry = if detail.is_empty() {
        reason.to_string()
    } else {
        format!("{reason}: {detail}")
    };
    if requested_a_compiled_lane() {
        eprintln!("[engine-demotion] reason={reason} detail={detail}");
    }
    if let Ok(mut list) = demotions().lock() {
        list.push(entry);
    }
}

/// Every demotion recorded so far, joined for the receipt line.
fn demotion_summary() -> Option<String> {
    let list = demotions().lock().ok()?;
    if list.is_empty() {
        return None;
    }
    Some(list.join("; "))
}

/// The receipt line, or `None` when no engine ever executed.
///
/// Exposed separately from [`emit`] so tests can assert on the exact text
/// without capturing stderr.
pub fn receipt_line(file: &str) -> Option<String> {
    let engine = engine()?;
    let requested = requested_mode().unwrap_or_else(|| "default".to_string());
    let demotion = demotion_summary();
    Some(format!(
        "[engine-receipt] engine={} requested={} demoted={} reason={} file={}",
        engine.as_str(),
        requested,
        if demotion.is_some() { "yes" } else { "no" },
        demotion.as_deref().unwrap_or("-"),
        file
    ))
}

/// Is a receipt requested for this process?
pub fn enabled() -> bool {
    matches!(
        std::env::var("SIMPLE_ENGINE_RECEIPT").ok().as_deref(),
        Some("1") | Some("true") | Some("yes")
    )
}

/// Print the receipt on stderr when `SIMPLE_ENGINE_RECEIPT=1`.
///
/// Cheap when off: a single environment lookup. Stderr rather than stdout so a
/// program's own output stays byte-identical and existing consumers that parse
/// stdout are unaffected.
pub fn emit(file: &str) {
    if !enabled() {
        return;
    }
    match receipt_line(file) {
        Some(line) => eprintln!("{line}"),
        // An engine field that was never stamped is itself the finding: it
        // means execution took a path with no receipt wired. Say so rather than
        // printing nothing, which would be indistinguishable from the feature
        // being off.
        None => eprintln!(
            "[engine-receipt] engine=unstamped requested={} demoted={} reason={} file={}",
            requested_mode().unwrap_or_else(|| "default".to_string()),
            if demotion_summary().is_some() { "yes" } else { "no" },
            demotion_summary().as_deref().unwrap_or("-"),
            file
        ),
    }
}

/// Test-only reset. Not `pub(crate)` because the driver's own integration tests
/// need it; it cannot forge an engine, only clear the record.
pub fn reset_for_test() {
    ENGINE.store(0, Ordering::SeqCst);
    if let Ok(mut list) = demotions().lock() {
        list.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The engine names are a stable wire format: the test runner and CI grep
    /// for them, so a rename is a breaking change and must fail here first.
    #[test]
    fn engine_names_are_stable() {
        assert_eq!(Engine::Interpreter.as_str(), "interpreter");
        assert_eq!(Engine::CraneliftJit.as_str(), "cranelift-jit");
        assert_eq!(Engine::LlvmJit.as_str(), "llvm-jit");
        assert_eq!(Engine::Native.as_str(), "native");
        assert_eq!(Engine::Wasm.as_str(), "wasm");
    }

    /// A demotion must survive into the receipt with its reason, and the last
    /// engine stamped -- the one that really ran -- must be what is reported.
    #[test]
    fn receipt_reports_the_engine_that_actually_ran_not_the_one_requested() {
        reset_for_test();
        stamp(Engine::CraneliftJit);
        record_demotion("jit-bail:generator", "for-in over gen fn");
        stamp(Engine::Interpreter);
        let line = receipt_line("/tmp/x.spl").expect("engine was stamped");
        assert!(line.contains("engine=interpreter"), "{line}");
        assert!(line.contains("demoted=yes"), "{line}");
        assert!(line.contains("jit-bail:generator"), "{line}");
        reset_for_test();
    }

    /// The complement: a clean run must NOT claim a demotion. A receipt that
    /// said the same thing in both cases would be worthless.
    #[test]
    fn a_clean_run_reports_no_demotion() {
        reset_for_test();
        stamp(Engine::CraneliftJit);
        let line = receipt_line("/tmp/x.spl").expect("engine was stamped");
        assert!(line.contains("engine=cranelift-jit"), "{line}");
        assert!(line.contains("demoted=no"), "{line}");
        assert!(line.contains("reason=-"), "{line}");
        reset_for_test();
    }

    /// An unstamped run is reported as `unstamped`, never as silence: silence
    /// is indistinguishable from the receipt being switched off.
    #[test]
    fn an_unstamped_run_has_no_receipt_line() {
        reset_for_test();
        assert!(receipt_line("/tmp/x.spl").is_none());
    }

    /// The UNSET case must count as a compiled-lane request, because the seed's
    /// default lane IS the JIT. Getting this backwards would leave the most
    /// common demotion path silent -- the exact defect being fixed.
    #[test]
    fn the_default_lane_counts_as_a_compiled_lane() {
        let saved = std::env::var("SIMPLE_EXECUTION_MODE").ok();
        std::env::remove_var("SIMPLE_EXECUTION_MODE");
        assert!(
            requested_a_compiled_lane(),
            "no explicit mode means the default JIT lane, so a demotion from it must be announced"
        );
        std::env::set_var("SIMPLE_EXECUTION_MODE", "interpret");
        assert!(
            !requested_a_compiled_lane(),
            "an explicit interpreter request has nothing to betray"
        );
        std::env::set_var("SIMPLE_EXECUTION_MODE", "jit");
        assert!(requested_a_compiled_lane());
        match saved {
            Some(v) => std::env::set_var("SIMPLE_EXECUTION_MODE", v),
            None => std::env::remove_var("SIMPLE_EXECUTION_MODE"),
        }
    }
}
