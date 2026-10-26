//! Fail-closed Rust twins of the C-only `rt_gpu_provider_*` owned-session API
//! (`src/runtime/runtime_dynload.c`). The Rust runtime has no GPU provider
//! dynload path of its own -- these are dual-implementation-ratchet twins,
//! not a port of the dynload/session-token machinery. Each function returns
//! exactly the value the C implementation returns on its own "no provider /
//! not authenticated / no session" fail path, so a caller sees identical
//! behaviour whether it is linked against the C runtime or this crate.
//!
//! Every C sibling begins by resolving `SimpleGpuProviderState` for
//! `backend_bit` and bails out to the same fail value whenever that state is
//! absent, not yet `ACTIVE`, or not authenticated -- which is always true
//! here, since this crate never populates that table.

/// Contract: `int64_t rt_gpu_provider_session_open(int64_t backend_bit, int64_t device)`
/// (`src/runtime/runtime_dynload.c:764`). C returns `0` (no session token)
/// whenever `device < 0` or the provider ABI cannot be acquired for
/// `backend_bit` -- the same "invalid device or no provider" path an
/// unauthenticated/absent GPU provider always takes. Fail-closed twin; no
/// Rust GPU provider.
#[no_mangle]
pub extern "C" fn rt_gpu_provider_session_open(_backend_bit: i64, _device: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_quarantine_drain(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:857`). With no session ever opened for
/// `backend_bit` (true here, since this crate owns no session table), C's
/// scan loop finds no matching token on its first pass and returns
/// `SIMPLE_GPU_STATUS_OK` (`0`) at line 876 -- "nothing to drain", the exact
/// state a GPU-less runtime is always in. Fail-closed twin; no Rust GPU
/// provider.
#[no_mangle]
pub extern "C" fn rt_gpu_provider_quarantine_drain(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_capability_bits(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:1403`). C returns `0` unless the provider
/// state is `ACTIVE` *and* `authenticated`, which never holds without a
/// loaded provider. Fail-closed twin; no Rust GPU provider.
#[no_mangle]
pub extern "C" fn rt_gpu_provider_capability_bits(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_identity(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:1416`). Same `ACTIVE && authenticated`
/// gate as `rt_gpu_provider_capability_bits`; C's fail value is `0`.
/// Fail-closed twin; no Rust GPU provider.
#[no_mangle]
pub extern "C" fn rt_gpu_provider_identity(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_generation(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:1429`). Same `ACTIVE && authenticated`
/// gate; C's fail value is `0`. Fail-closed twin; no Rust GPU provider.
#[no_mangle]
pub extern "C" fn rt_gpu_provider_generation(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_artifact_digest_word(int64_t backend_bit, int64_t word)`
/// (`src/runtime/runtime_dynload.c:1442`). C returns `0` both for an
/// out-of-range `word` (`< 0 || >= 4`) and for the same
/// `ACTIVE && authenticated` gate as the other accessors. Fail-closed twin;
/// no Rust GPU provider.
#[no_mangle]
pub extern "C" fn rt_gpu_provider_artifact_digest_word(_backend_bit: i64, _word: i64) -> i64 {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn session_open_is_sentinel_zero() {
        assert_eq!(rt_gpu_provider_session_open(1, 0), 0);
        assert_eq!(rt_gpu_provider_session_open(-1, -1), 0);
    }

    #[test]
    fn quarantine_drain_reports_ok_nothing_to_drain() {
        assert_eq!(rt_gpu_provider_quarantine_drain(1), 0);
    }

    #[test]
    fn accessors_are_sentinel_zero() {
        assert_eq!(rt_gpu_provider_capability_bits(1), 0);
        assert_eq!(rt_gpu_provider_identity(1), 0);
        assert_eq!(rt_gpu_provider_generation(1), 0);
        assert_eq!(rt_gpu_provider_artifact_digest_word(1, 0), 0);
        assert_eq!(rt_gpu_provider_artifact_digest_word(1, 99), 0);
    }
}
