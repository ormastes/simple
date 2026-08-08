//! UTF-8 slice-boundary audit — COUNTING MODE.
//!
//! Bug: text slicing splits UTF-8 mid-codepoint and stores the invalid bytes
//! with no validation (`doc/08_tracking/bug/`). Five independent slice
//! implementations disagree about what happens (raw / lossy / clamped), and
//! stdout's sanitizer renders every one of them identically, so the defect is
//! invisible in printed output — only the bytes show it.
//!
//! This module is **stage 1** of the rollout: every slice implementation
//! reports the bytes it is about to return, this module decides whether the
//! slice CREATED invalid UTF-8, and records it. **Nothing fails.** The hard
//! error is stage 4 and is only enabled once the measured blast radius over a
//! real workload is zero or a justified residual.
//!
//! ## Gate — DEFAULT OFF
//!
//! `SIMPLE_UTF8_SLICE_AUDIT`
//! * unset / `0` — disabled. One relaxed atomic load per slice; no validation,
//!   no allocation, no output.
//! * `1` — count every violation; log the FIRST occurrence per site.
//! * `2` — count every violation; log EVERY occurrence.
//!
//! ## Violation definition
//!
//! A violation is recorded only when the source bytes were valid UTF-8 and the
//! returned bytes are not. Slicing an already-invalid string is not attributed
//! to the slice, so the count measures what THIS defect causes rather than
//! inheriting unrelated corruption.
//!
//! ## Log line (stderr, one per violation, machine-readable)
//!
//! ```text
//! SIMPLE_UTF8_SLICE_AUDIT site=<id> start=<i> end=<i> srclen=<n> outlen=<n>
//! ```

use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};

/// Stable site identifiers. Each slice implementation reports under its own
/// id so the measured blast radius can be attributed per implementation.
pub mod site {
    /// `Expr::Slice` string arm, Rust interpreter (`s[a:b]`).
    pub const INTERP_BRACKET: u8 = 0;
    /// `.slice()` / `.substring()` string method, Rust interpreter.
    pub const INTERP_METHOD: u8 = 1;
    /// `rt_slice` string arm, Rust runtime (Cranelift JIT / default engine).
    pub const RT_SLICE_RUST: u8 = 2;
    /// Synthetic violation emitted once per enabled process. Not a real site.
    pub const SELF_TEST: u8 = 3;

    pub fn name(id: u8) -> &'static str {
        match id {
            INTERP_BRACKET => "interp_bracket",
            INTERP_METHOD => "interp_method",
            RT_SLICE_RUST => "rt_slice_rust",
            SELF_TEST => "self_test",
            _ => "unknown",
        }
    }
}

const LEVEL_UNREAD: u8 = u8::MAX;

static LEVEL: AtomicU8 = AtomicU8::new(LEVEL_UNREAD);
static VIOLATIONS: AtomicU64 = AtomicU64::new(0);
/// One bit per site id — used for the level-1 "first occurrence only" filter.
static SEEN_SITES: AtomicU64 = AtomicU64::new(0);

/// Current audit level. Reads the environment once, then caches.
#[inline]
pub fn level() -> u8 {
    let cached = LEVEL.load(Ordering::Relaxed);
    if cached != LEVEL_UNREAD {
        return cached;
    }
    let parsed = match std::env::var("SIMPLE_UTF8_SLICE_AUDIT").ok().as_deref() {
        Some("1") => 1,
        Some("2") => 2,
        _ => 0,
    };
    LEVEL.store(parsed, Ordering::Relaxed);
    if parsed != 0 {
        // Liveness control, emitted ONCE per enabled process, in the same
        // process as the measurement. A count of zero from a check that never
        // ran is indistinguishable from a real zero, so every measured run
        // carries its own synthetic true positive. Subtract exactly one
        // `site=self_test` line per process from any total.
        self_test();
    }
    parsed
}

#[inline]
pub fn enabled() -> bool {
    level() != 0
}

/// Total violations recorded so far in this process.
pub fn violations() -> u64 {
    VIOLATIONS.load(Ordering::Relaxed)
}

/// Report the bytes a slice is about to return.
///
/// Returns `true` when this slice created invalid UTF-8 (i.e. a violation was
/// recorded). Callers MUST NOT change behaviour on the return value while the
/// rollout is in counting mode — it exists so stage 4 can flip to an error at
/// exactly these call sites.
#[inline]
pub fn note(site_id: u8, start: i64, end: i64, src: &[u8], out: &[u8]) -> bool {
    if level() == 0 {
        return false;
    }
    note_slow(site_id, start, end, src, out)
}

#[cold]
fn note_slow(site_id: u8, start: i64, end: i64, src: &[u8], out: &[u8]) -> bool {
    // Validate the OUTPUT first: the common case is a valid slice, and that
    // check is the cheap one when the slice is short.
    if std::str::from_utf8(out).is_ok() {
        return false;
    }
    // Only attribute the breakage to the slice when the source was itself
    // well-formed; otherwise this is inherited corruption, not this defect.
    if std::str::from_utf8(src).is_err() {
        return false;
    }

    VIOLATIONS.fetch_add(1, Ordering::Relaxed);

    let bit = 1u64 << (site_id & 63);
    let first_for_site = (SEEN_SITES.fetch_or(bit, Ordering::Relaxed) & bit) == 0;
    if level() >= 2 || first_for_site {
        eprintln!(
            "SIMPLE_UTF8_SLICE_AUDIT site={} start={} end={} srclen={} outlen={}",
            site::name(site_id),
            start,
            end,
            src.len(),
            out.len()
        );
    }
    true
}

/// Force a synthetic violation, used to prove the counter is LIVE in the same
/// process as a measurement run: a count of zero from an inert check is
/// indistinguishable from a real zero. Honours the gate like any other site.
pub fn self_test() -> bool {
    // "é" = C3 A9; [0:1] keeps the lead byte only.
    let src: &[u8] = b"\xc3\xa9";
    note_slow(site::SELF_TEST, 0, 1, src, &src[0..1])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disabled_by_default_records_nothing() {
        // LEVEL is process-global; this test only asserts the pure predicate
        // that a well-formed slice is never a violation regardless of level.
        let src = "abc".as_bytes();
        assert!(!note(site::INTERP_BRACKET, 0, 2, src, &src[0..2]));
    }
}
