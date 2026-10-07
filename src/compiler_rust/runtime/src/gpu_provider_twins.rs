//! GPU provider ABI selection: native-all uses the canonical C registry.
//! Other configurations retain fail-closed Rust twins of the owned-session API
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
#[cfg(not(feature = "native-all-provider"))]
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
#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_gpu_provider_quarantine_drain(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_capability_bits(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:1403`). C returns `0` unless the provider
/// state is `ACTIVE` *and* `authenticated`, which never holds without a
/// loaded provider. Fail-closed twin; no Rust GPU provider.
#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_gpu_provider_capability_bits(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_identity(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:1416`). Same `ACTIVE && authenticated`
/// gate as `rt_gpu_provider_capability_bits`; C's fail value is `0`.
/// Fail-closed twin; no Rust GPU provider.
#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_gpu_provider_identity(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_generation(int64_t backend_bit)`
/// (`src/runtime/runtime_dynload.c:1429`). Same `ACTIVE && authenticated`
/// gate; C's fail value is `0`. Fail-closed twin; no Rust GPU provider.
#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_gpu_provider_generation(_backend_bit: i64) -> i64 {
    0
}

/// Contract: `int64_t rt_gpu_provider_artifact_digest_word(int64_t backend_bit, int64_t word)`
/// (`src/runtime/runtime_dynload.c:1442`). C returns `0` both for an
/// out-of-range `word` (`< 0 || >= 4`) and for the same
/// `ACTIVE && authenticated` gate as the other accessors. Fail-closed twin;
/// no Rust GPU provider.
#[cfg(not(feature = "native-all-provider"))]
#[no_mangle]
pub extern "C" fn rt_gpu_provider_artifact_digest_word(_backend_bit: i64, _word: i64) -> i64 {
    0
}

#[cfg(all(test, not(feature = "native-all-provider")))]
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

// Raw C contracts: integer arguments are untagged ABI words. The path result
// is a borrowed thread-local C string, not a managed Simple Text.
#[cfg(feature = "native-all-provider")]
pub(crate) mod linked_registry {
    unsafe extern "C" {
        pub fn rt_gpu_provider_loaded(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_abi_version(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_backend_bits(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_capability_bits(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_identity(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_generation(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_artifact_digest_word(backend_bit: i64, word: i64) -> i64;
        pub fn rt_gpu_provider_path(backend_bit: i64) -> *const std::ffi::c_char;
        pub fn rt_gpu_provider_unload(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_session_open(backend_bit: i64, device: i64) -> i64;
        pub fn rt_gpu_provider_session_close(backend_bit: i64, session: i64) -> i64;
        pub fn rt_gpu_provider_resource_alloc(
            backend_bit: i64,
            session: i64,
            size_bytes: i64,
            flags: i64,
            usage_bits: i64,
        ) -> i64;
        pub fn rt_gpu_provider_resource_release(backend_bit: i64, session: i64, resource: i64) -> i64;
        pub fn rt_gpu_provider_submit_raw(
            backend_bit: i64,
            session: i64,
            resource: i64,
            format: i64,
            data: i64,
            length: i64,
            correlation_id: i64,
        ) -> i64;
        pub fn rt_gpu_provider_wait_raw(
            backend_bit: i64,
            session: i64,
            completion: i64,
            timeout_ns: i64,
            receipt_ptr: i64,
        ) -> i64;
        pub fn rt_gpu_provider_readback_raw(backend_bit: i64, session: i64, resource: i64, bytes_ptr: i64) -> i64;
        pub fn rt_gpu_provider_completion_release(backend_bit: i64, session: i64, completion: i64) -> i64;
        pub fn rt_gpu_provider_quarantine_drain(backend_bit: i64) -> i64;
        pub fn rt_gpu_provider_session_authority_word(backend_bit: i64, session: i64, word: i64) -> i64;
        pub fn rt_gpu_provider_resource_authority_word(backend_bit: i64, session: i64, resource: i64, word: i64)
            -> i64;
        pub fn rt_gpu_provider_completion_authority_word(
            backend_bit: i64,
            session: i64,
            completion: i64,
            word: i64,
        ) -> i64;
        pub fn rt_gpu_provider_device_image_authority_word(
            backend_bit: i64,
            session: i64,
            image: i64,
            word: i64,
        ) -> i64;
    }
}

#[cfg(feature = "native-all-provider")]
pub extern "C" fn rt_gpu_provider_capability_bits(backend_bit: i64) -> i64 {
    unsafe { linked_registry::rt_gpu_provider_capability_bits(backend_bit) }
}

#[cfg(feature = "native-all-provider")]
pub extern "C" fn rt_gpu_provider_identity(backend_bit: i64) -> i64 {
    unsafe { linked_registry::rt_gpu_provider_identity(backend_bit) }
}

#[cfg(feature = "native-all-provider")]
pub extern "C" fn rt_gpu_provider_generation(backend_bit: i64) -> i64 {
    unsafe { linked_registry::rt_gpu_provider_generation(backend_bit) }
}

#[cfg(feature = "native-all-provider")]
pub extern "C" fn rt_gpu_provider_artifact_digest_word(backend_bit: i64, word: i64) -> i64 {
    unsafe { linked_registry::rt_gpu_provider_artifact_digest_word(backend_bit, word) }
}

#[cfg(feature = "native-all-provider")]
pub extern "C" fn rt_gpu_provider_session_open(backend_bit: i64, device: i64) -> i64 {
    unsafe { linked_registry::rt_gpu_provider_session_open(backend_bit, device) }
}

#[cfg(feature = "native-all-provider")]
pub extern "C" fn rt_gpu_provider_quarantine_drain(backend_bit: i64) -> i64 {
    unsafe { linked_registry::rt_gpu_provider_quarantine_drain(backend_bit) }
}

#[cfg(all(test, feature = "native-all-provider", feature = "runtime-symbol-table"))]
mod native_registry_tests {
    use super::linked_registry;

    #[test]
    fn every_gpu_registry_lookup_has_one_exact_c_owner() {
        let expected: &[(&str, *const u8)] = &[
            (
                "rt_gpu_provider_loaded",
                linked_registry::rt_gpu_provider_loaded as *const u8,
            ),
            (
                "rt_gpu_provider_abi_version",
                linked_registry::rt_gpu_provider_abi_version as *const u8,
            ),
            (
                "rt_gpu_provider_backend_bits",
                linked_registry::rt_gpu_provider_backend_bits as *const u8,
            ),
            (
                "rt_gpu_provider_capability_bits",
                linked_registry::rt_gpu_provider_capability_bits as *const u8,
            ),
            (
                "rt_gpu_provider_identity",
                linked_registry::rt_gpu_provider_identity as *const u8,
            ),
            (
                "rt_gpu_provider_generation",
                linked_registry::rt_gpu_provider_generation as *const u8,
            ),
            (
                "rt_gpu_provider_artifact_digest_word",
                linked_registry::rt_gpu_provider_artifact_digest_word as *const u8,
            ),
            (
                "rt_gpu_provider_path",
                linked_registry::rt_gpu_provider_path as *const u8,
            ),
            (
                "rt_gpu_provider_unload",
                linked_registry::rt_gpu_provider_unload as *const u8,
            ),
            (
                "rt_gpu_provider_session_open",
                linked_registry::rt_gpu_provider_session_open as *const u8,
            ),
            (
                "rt_gpu_provider_session_close",
                linked_registry::rt_gpu_provider_session_close as *const u8,
            ),
            (
                "rt_gpu_provider_resource_alloc",
                linked_registry::rt_gpu_provider_resource_alloc as *const u8,
            ),
            (
                "rt_gpu_provider_resource_release",
                linked_registry::rt_gpu_provider_resource_release as *const u8,
            ),
            (
                "rt_gpu_provider_submit_raw",
                linked_registry::rt_gpu_provider_submit_raw as *const u8,
            ),
            (
                "rt_gpu_provider_wait_raw",
                linked_registry::rt_gpu_provider_wait_raw as *const u8,
            ),
            (
                "rt_gpu_provider_readback_raw",
                linked_registry::rt_gpu_provider_readback_raw as *const u8,
            ),
            (
                "rt_gpu_provider_completion_release",
                linked_registry::rt_gpu_provider_completion_release as *const u8,
            ),
            (
                "rt_gpu_provider_quarantine_drain",
                linked_registry::rt_gpu_provider_quarantine_drain as *const u8,
            ),
            (
                "rt_gpu_provider_session_authority_word",
                linked_registry::rt_gpu_provider_session_authority_word as *const u8,
            ),
            (
                "rt_gpu_provider_resource_authority_word",
                linked_registry::rt_gpu_provider_resource_authority_word as *const u8,
            ),
            (
                "rt_gpu_provider_completion_authority_word",
                linked_registry::rt_gpu_provider_completion_authority_word as *const u8,
            ),
            (
                "rt_gpu_provider_device_image_authority_word",
                linked_registry::rt_gpu_provider_device_image_authority_word as *const u8,
            ),
        ];
        for &(name, owner) in expected {
            let entries: Vec<_> = crate::RUNTIME_SYMBOL_ENTRIES
                .iter()
                .filter(|entry| entry.name == name)
                .collect();
            assert_eq!(entries.len(), 1, "{name} must have exactly one lookup entry");
            assert!(!owner.is_null());
            assert_eq!(entries[0].ptr, owner, "{name} must resolve to the C registry");
        }
        let open = crate::RUNTIME_SYMBOL_ENTRIES
            .iter()
            .find(|entry| entry.name == "rt_gpu_provider_session_open")
            .unwrap();
        let open: unsafe extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(open.ptr) };
        // Invalid device rejects before any provider load. Real authenticated
        // device execution is separately qualified against the resulting archive.
        assert_eq!(unsafe { open(1, -1) }, 0);
    }
}
