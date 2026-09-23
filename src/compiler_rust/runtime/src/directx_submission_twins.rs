//! Fail-closed Rust twins of the C-only `rt_directx_submission_*` DirectX 11
//! capsule API (`src/runtime/runtime_directx_core.c`). The Rust runtime has
//! no DirectX submission-lifecycle machinery of its own -- these are
//! dual-implementation-ratchet twins, not a port of the Windows D3D11
//! device/event-query bookkeeping. The five externally-callable functions
//! return exactly what the C implementation returns on ITS OWN non-Windows
//! stub path (`#else` branch, `runtime_directx_core.c:633-684`), so a caller
//! sees identical behaviour whether it is linked against the C runtime on a
//! non-Windows host or this crate. The six remaining names are Windows-only
//! internal `static` bookkeeping helpers (`runtime_directx_core.c:129-186`,
//! inside `#if defined(_WIN32)`) with no public contract and no non-Windows
//! C counterpart at all; their twins are `pub(crate)` no-ops that mirror the
//! same "no real submission ever exists" fail-closed posture, kept private
//! so this crate does not export a global symbol the C build never exports
//! either.

/// Contract: `int64_t rt_directx_submission_poll(int64_t submission_id)`
/// (`runtime_directx_core.c:660`). C's non-Windows stub always returns `-1`
/// (no submission ever exists to poll). Fail-closed twin; no Rust DirectX
/// device.
#[no_mangle]
pub extern "C" fn rt_directx_submission_poll(_submission_id: i64) -> i64 {
    -1
}

/// Contract: `int64_t rt_directx_submission_complete(int64_t submission_id)`
/// (`runtime_directx_core.c:665`). Same `-1` fail-closed stub as `poll`.
#[no_mangle]
pub extern "C" fn rt_directx_submission_complete(_submission_id: i64) -> i64 {
    -1
}

/// Contract: `int64_t rt_directx_submission_retire(int64_t submission_id)`
/// (`runtime_directx_core.c:670`). Same `-1` fail-closed stub.
#[no_mangle]
pub extern "C" fn rt_directx_submission_retire(_submission_id: i64) -> i64 {
    -1
}

/// Contract: `int64_t rt_directx_submission_abandon(int64_t submission_id)`
/// (`runtime_directx_core.c:675`). C's non-Windows stub returns `0`
/// (abandoning a submission that never existed is trivially successful),
/// unlike its `poll`/`complete`/`retire` siblings which return `-1`.
#[no_mangle]
pub extern "C" fn rt_directx_submission_abandon(_submission_id: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_directx_submission_readback_pixel(int64_t
/// submission_id)` (`runtime_directx_core.c:680`). Same `-1` fail-closed
/// stub as `poll`/`complete`/`retire`.
#[no_mangle]
pub extern "C" fn rt_directx_submission_readback_pixel(_submission_id: i64) -> i64 {
    -1
}

// ---------------------------------------------------------------------------
// Windows-only internal bookkeeping helpers. C declares each of these
// `static` inside `#if defined(_WIN32)` (runtime_directx_core.c:129-186) --
// they have no non-Windows counterpart and no external linkage on the C
// side either. Kept `pub(crate)` (not `#[no_mangle]`) so this crate does not
// export a global symbol the C build never exports.
// ---------------------------------------------------------------------------

/// Contract: `static RtDirectXSubmission *rt_directx_submission_find(int64_t
/// id)` (`runtime_directx_core.c:129`). Walks the live submission list for
/// `id`. This lane tracks no submissions, so there is never a match.
#[allow(dead_code)]
pub(crate) fn rt_directx_submission_find(_id: i64) -> Option<()> {
    None
}

/// Contract: `static int rt_directx_submission_was_retired(int64_t id)`
/// (`runtime_directx_core.c:138`). Scans the bounded retired-id cache.
/// Nothing is ever retired on this lane, so the answer is always "no".
#[allow(dead_code)]
pub(crate) fn rt_directx_submission_was_retired(_id: i64) -> bool {
    false
}

/// Contract: `static void rt_directx_submission_note_retired(int64_t id)`
/// (`runtime_directx_core.c:146`). Records `id` into the retired-id cache.
/// No cache exists on this lane, so there is nothing to record.
#[allow(dead_code)]
pub(crate) fn rt_directx_submission_note_retired(_id: i64) {}

/// Contract: `static void rt_directx_submission_release(RtDirectXSubmission
/// *submission)` (`runtime_directx_core.c:160`). Releases the COM resources
/// (query/staging/view/target/device) owned by a submission. No COM
/// resources are ever allocated on this lane, so there is nothing to
/// release.
#[allow(dead_code)]
pub(crate) fn rt_directx_submission_release(_submission: Option<()>) {}

/// Contract: `static void rt_directx_submission_unlink_and_free
/// (RtDirectXSubmission *submission)` (`runtime_directx_core.c:152`).
/// Unlinks a submission from the live list and frees it. No live list
/// exists on this lane, so there is nothing to unlink or free.
#[allow(dead_code)]
pub(crate) fn rt_directx_submission_unlink_and_free(_submission: Option<()>) {}

/// Contract: `static int rt_directx_submission_poll_locked
/// (RtDirectXSubmission *submission)` (`runtime_directx_core.c:172`).
/// Polls a submission's D3D11 event query while the lock is held; returns
/// `-1` on a null submission or a missing event query/context -- exactly
/// this lane's permanent state, since no submission or device is ever
/// created here.
#[allow(dead_code)]
pub(crate) fn rt_directx_submission_poll_locked(_submission: Option<()>) -> i64 {
    -1
}
