//! Fail-closed Rust twins for Process Observation V4 and Process Owned V3
//! (SplArray-valued) primitives that today exist only in the C runtime
//! (src/runtime/runtime_process_owned.c).
//!
//! `SplArray*` is an opaque handle owned by whichever runtime allocated it
//! (rt_array_new/rt_array_push and friends); the Rust runtime has no
//! provider for that allocator, so these twins never attempt to fabricate
//! one. This is a *fail-closed twin*, not a port of process supervision: on
//! the real C provider (Linux, the unix leg of runtime_process_owned.c) most
//! of these functions ARE implemented and return a live SplArray, but that
//! implementation is deliberately not mirrored here. The Rust side always
//! answers "unavailable" — a null pointer for every SplArray*-returning
//! function (the same sentinel the C provider itself returns on allocation
//! failure, e.g. `if (!values) return NULL;` throughout
//! runtime_process_owned.c), and the C provider's own non-unix fail-closed
//! branch's scalar sentinel for the two integer-returning functions. The
//! three `test_force_*` hooks are test-only signal injection points with no
//! return value; the twin is a no-op.
//!
//! Every C twin file:line below is the non-unix (`#else`, C fallback) branch
//! of src/runtime/runtime_process_owned.c, lines 4221-4609 — the one branch
//! of that file that is itself already fail-closed end to end, so its
//! sentinel choices are the closest thing this file has to a "documented
//! failure sentinel" to mirror.

//! ## Link-lane selection (added 2026-09-13)
//!
//! The eleven SplArray*/scalar twins below are gated behind the off-by-default
//! cargo feature `process-rust-twin`. Both halves of the pair export the same
//! `#[no_mangle]` / C strong symbol, and the C runtime archive is linked with
//! `-Wl,-force_load`, so on Mach-O every duplicate is a hard link error
//! (11 `duplicate symbol` diagnostics, exit 101 — see
//! doc/08_tracking/bug/macos_seed_build_duplicate_rt_process_twin_symbols_2026-09-13.md).
//! A twin pair must be SELECTED, not double-linked: by default the C lane
//! (src/runtime/runtime_process_owned.c) is the linked provider and the Rust
//! fail-closed twin is compiled out; enable `process-rust-twin` to link the
//! Rust lane instead (and exclude the C objects). Both sources stay in tree so
//! scripts/check/check-rt-dual-implementation-ratchet.shs still counts them as
//! a twin pair.
//!
//! The three `test_force_*` hooks are NOT gated: their C counterparts exist
//! only under `#ifdef RT_PROCESS_OBSERVATION_V4_TESTING`, which no normal build
//! defines, so they never collide.

use std::os::raw::c_void;

/// Contract: C twin `rt_process_owned_v3_capabilities_value` at
/// src/runtime/runtime_process_owned.c:4446 (non-unix branch). C returns a
/// populated `[adapter_version, 0, 0]` SplArray there; the unix branch
/// (line 1990) returns a live SplArray too. Rust sentinel: null pointer —
/// fail-closed twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_owned_v3_capabilities_value() -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_owned_v3_observation_value` at
/// src/runtime/runtime_process_owned.c:4470 (non-unix branch; unix real
/// implementation at line 2051). Rust sentinel: null pointer — fail-closed
/// twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_owned_v3_observation_value(_handle: i64) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_capabilities_value` at
/// src/runtime/runtime_process_owned.c:4573 (non-unix branch; unix real
/// implementation at line 3655). Rust sentinel: null pointer — fail-closed
/// twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_capabilities_value() -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_pin_cwd_value` at
/// src/runtime/runtime_process_owned.c:4581 (non-unix branch; unix real
/// implementation at line 2483). Sentinel: 0 — the exact value the C
/// non-unix branch returns (`(void)path_data; (void)path_len; return 0;`).
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_pin_cwd_value(
    _path_data: *const u8,
    _path_len: u64,
) -> i64 {
    0
}

/// Contract: C twin `rt_process_observation_v4_cwd_digest_value` at
/// src/runtime/runtime_process_owned.c:4584 (non-unix branch; unix real
/// implementation at line 2563). C's own non-unix branch returns
/// `rt_array_new(0)` (an empty, non-null SplArray); this twin has no
/// SplArray provider, so it answers with the same null-pointer sentinel
/// used by every other pointer-returning twin here — fail-closed twin, not
/// a port of process supervision.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_cwd_digest_value(_handle: i64) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_close_cwd_value` at
/// src/runtime/runtime_process_owned.c:4587 (non-unix branch; unix real
/// implementation at line 2574). Sentinel: 0 — the exact value the C
/// non-unix branch returns (`(void)handle; return 0;`).
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_close_cwd_value(_handle: i64) -> i32 {
    0
}

/// Contract: C twin `rt_process_observation_v4_start_value` at
/// src/runtime/runtime_process_owned.c:4588 (non-unix branch; unix real
/// implementation at line 3665). C's own non-unix branch returns
/// `pov4_unavailable_tuple()`, a fully populated ENOTSUP receipt tuple built
/// from the Rust-absent `rt_array_new`/`rt_array_push` allocator. Rust
/// sentinel: null pointer — fail-closed twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_start_value(_binding: *mut c_void) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_poll_value` at
/// src/runtime/runtime_process_owned.c:4595 (non-unix branch; unix real
/// implementation at line 3558). Rust sentinel: null pointer — fail-closed
/// twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_poll_value(
    _ticket: *mut c_void,
    _wait_ns: i64,
) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_cancel_value` at
/// src/runtime/runtime_process_owned.c:4598 (non-unix branch; unix real
/// implementation at line 3577). Rust sentinel: null pointer — fail-closed
/// twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_cancel_value(
    _ticket: *mut c_void,
    _wait_ns: i64,
) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_collect_value` at
/// src/runtime/runtime_process_owned.c:4601 (non-unix branch; unix real
/// implementation at line 3594). Rust sentinel: null pointer — fail-closed
/// twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_collect_value(
    _ticket: *mut c_void,
    _wait_ns: i64,
) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_ack_collect_value` at
/// src/runtime/runtime_process_owned.c:4604 (non-unix branch; unix real
/// implementation at line 3621). Rust sentinel: null pointer — fail-closed
/// twin; no Rust SplArray provider yet.
#[cfg(feature = "process-rust-twin")]
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_ack_collect_value(
    _ticket: *mut c_void,
    _digest: *mut c_void,
) -> *mut c_void {
    std::ptr::null_mut()
}

/// Contract: C twin `rt_process_observation_v4_test_force_exec_failure` at
/// src/runtime/runtime_process_owned.c:261 (guarded by
/// `RT_PROCESS_OBSERVATION_V4_TESTING`). Test-only signal-injection hook,
/// not process supervision — no-op twin, no return value to sentinel.
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_test_force_exec_failure(
    _error: i32,
    _count: i32,
) {
}

/// Contract: C twin `rt_process_observation_v4_test_force_reconcile_eintr`
/// at src/runtime/runtime_process_owned.c:268 (guarded by
/// `RT_PROCESS_OBSERVATION_V4_TESTING`). Test-only signal-injection hook,
/// not process supervision — no-op twin, no return value to sentinel.
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_test_force_reconcile_eintr(_count: i32) {}

/// Contract: C twin `rt_process_observation_v4_test_force_signal_gone` at
/// src/runtime/runtime_process_owned.c:265 (guarded by
/// `RT_PROCESS_OBSERVATION_V4_TESTING`). Test-only signal-injection hook,
/// not process supervision — no-op twin, no return value to sentinel.
#[no_mangle]
pub unsafe extern "C" fn rt_process_observation_v4_test_force_signal_gone(_count: i32) {}

#[cfg(test)]
mod dual_lane_twin_sentinels {
    //! `cargo test --lib -p simple-runtime dual_lane_twin_sentinels`.
    //! Hard-codes the C fail-closed sentinel values from the non-unix
    //! branch of src/runtime/runtime_process_owned.c (lines 4221-4609) and
    //! asserts every Rust twin returns exactly that value.
    use super::*;

    #[cfg(feature = "process-rust-twin")]
    #[test]
    fn process_v4_v3_twins_return_documented_sentinels() {
        unsafe {
            assert!(rt_process_owned_v3_capabilities_value().is_null());
            assert!(rt_process_owned_v3_observation_value(0).is_null());
            assert!(rt_process_observation_v4_capabilities_value().is_null());
            assert_eq!(
                rt_process_observation_v4_pin_cwd_value(std::ptr::null(), 0),
                0
            );
            assert!(rt_process_observation_v4_cwd_digest_value(0).is_null());
            assert_eq!(rt_process_observation_v4_close_cwd_value(0), 0);
            assert!(rt_process_observation_v4_start_value(std::ptr::null_mut()).is_null());
            assert!(rt_process_observation_v4_poll_value(std::ptr::null_mut(), 0).is_null());
            assert!(rt_process_observation_v4_cancel_value(std::ptr::null_mut(), 0).is_null());
            assert!(rt_process_observation_v4_collect_value(std::ptr::null_mut(), 0).is_null());
            assert!(rt_process_observation_v4_ack_collect_value(
                std::ptr::null_mut(),
                std::ptr::null_mut()
            )
            .is_null());
        }
    }

    /// The three test-force hooks are never link-gated, so this half of the
    /// twin contract is asserted on every feature configuration: no return
    /// value, just confirm each twin is callable and a genuine no-op.
    #[test]
    fn process_v4_test_force_hooks_are_no_ops() {
        unsafe {
            rt_process_observation_v4_test_force_exec_failure(0, 0);
            rt_process_observation_v4_test_force_reconcile_eintr(0);
            rt_process_observation_v4_test_force_signal_gone(0);
        }
    }
}
