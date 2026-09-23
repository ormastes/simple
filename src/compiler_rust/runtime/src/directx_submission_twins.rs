//! Fail-closed Rust twins of the C-only `rt_directx_submission_*` DirectX 11
//! capsule API (`src/runtime/runtime_directx_core.c`). The Rust runtime has
//! no DirectX submission-lifecycle machinery of its own -- these are
//! dual-implementation-ratchet twins, not a port of the Windows D3D11
//! device/event-query bookkeeping. The six Rust-callable functions
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
//!
//! `runtime_directx_core.c`, linked by build.rs on every target, is the sole
//! owner of the unmangled C ABI. These twins deliberately retain Rust symbol
//! mangling: exporting them would collide with C and could replace Windows'
//! real submission lifecycle with constant-return reference behavior.

/// Contract: `int64_t rt_directx_submission_submit(int64_t width, int64_t
/// height, const int64_t *words, int64_t words_len)`
/// (`runtime_directx_core.c:651`). C's non-Windows stub ignores every
/// argument and always returns `0` (no valid submission id is ever handed
/// out). Fail-closed twin; no Rust DirectX device. The pointer argument is
/// never dereferenced, matching the C stub.
pub extern "C" fn rt_directx_submission_submit(
    _width: i64,
    _height: i64,
    _words: *const i64,
    _words_len: i64,
) -> i64 {
    0
}

/// Contract: `int64_t rt_directx_submission_poll(int64_t submission_id)`
/// (`runtime_directx_core.c:660`). C's non-Windows stub always returns `-1`
/// (no submission ever exists to poll). Fail-closed twin; no Rust DirectX
/// device.
pub extern "C" fn rt_directx_submission_poll(_submission_id: i64) -> i64 {
    -1
}

/// Contract: `int64_t rt_directx_submission_complete(int64_t submission_id)`
/// (`runtime_directx_core.c:665`). Same `-1` fail-closed stub as `poll`.
pub extern "C" fn rt_directx_submission_complete(_submission_id: i64) -> i64 {
    -1
}

/// Contract: `int64_t rt_directx_submission_retire(int64_t submission_id)`
/// (`runtime_directx_core.c:670`). Same `-1` fail-closed stub.
pub extern "C" fn rt_directx_submission_retire(_submission_id: i64) -> i64 {
    -1
}

/// Contract: `int64_t rt_directx_submission_abandon(int64_t submission_id)`
/// (`runtime_directx_core.c:675`). C's non-Windows stub returns `0`
/// (abandoning a submission that never existed is trivially successful),
/// unlike its `poll`/`complete`/`retire` siblings which return `-1`.
pub extern "C" fn rt_directx_submission_abandon(_submission_id: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_directx_submission_readback_pixel(int64_t
/// submission_id)` (`runtime_directx_core.c:680`). Same `-1` fail-closed
/// stub as `poll`/`complete`/`retire`.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rust_twins_remain_callable_and_fail_closed() {
        for id in [-1, 0, 1, i64::MAX] {
            assert_eq!(rt_directx_submission_poll(id), -1);
            assert_eq!(rt_directx_submission_complete(id), -1);
            assert_eq!(rt_directx_submission_retire(id), -1);
            assert_eq!(rt_directx_submission_abandon(id), 0);
            assert_eq!(rt_directx_submission_readback_pixel(id), -1);
        }
    }

    // Force both the C object and Rust twins into one link. Besides catching
    // duplicate exports, real phase transitions prove that C owns the ABI.
    #[cfg(target_os = "windows")]
    #[test]
    #[ignore = "requires hardware D3D11; run check-directx-submission-abi-windows.cmd"]
    fn windows_c_abi_keeps_real_submission_lifecycle() {
        mod c {
            extern "C" {
                pub fn rt_directx_submission_submit(
                    width: i64, height: i64, words: *const i64, words_len: i64,
                ) -> i64;
                pub fn rt_directx_submission_poll(id: i64) -> i64;
                pub fn rt_directx_submission_complete(id: i64) -> i64;
                pub fn rt_directx_submission_retire(id: i64) -> i64;
                pub fn rt_directx_submission_abandon(id: i64) -> i64;
                pub fn rt_directx_submission_readback_pixel(id: i64) -> i64;
            }
        }
        let words = [0x44583131_i64, 1, 1, 12, 1, 8, 0, 0, 0, 0, 0xff102030, 0];
        unsafe {
            let id = c::rt_directx_submission_submit(1, 1, words.as_ptr(), words.len() as i64);
            assert!(id > 0, "a real D3D11 submission is required");
            assert_eq!(rt_directx_submission_poll(id), -1);
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
            let mut phase = c::rt_directx_submission_poll(id);
            while phase == 1 && std::time::Instant::now() < deadline {
                std::thread::sleep(std::time::Duration::from_millis(1));
                phase = c::rt_directx_submission_poll(id);
            }
            assert_eq!(phase, 2, "D3D11 event query must finish");
            assert_eq!(c::rt_directx_submission_readback_pixel(id), 0xff102030);
            assert_eq!(c::rt_directx_submission_complete(id), 3);
            assert_eq!(c::rt_directx_submission_retire(id), 4);
            assert_eq!(c::rt_directx_submission_poll(id), 4);
            assert_eq!(c::rt_directx_submission_abandon(id), 0);
            let abandoned = c::rt_directx_submission_submit(1, 1, words.as_ptr(), words.len() as i64);
            assert!(abandoned > 0);
            assert_eq!(c::rt_directx_submission_abandon(abandoned), 1);
            assert_eq!(c::rt_directx_submission_poll(abandoned), -1);
        }
    }
}
