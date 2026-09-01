//! Reserved cache-daemon host receipt ABI, version 1.
//!
//! These entrypoints deliberately fail closed. A later provider must bind peer
//! credentials to a transport descriptor, hold a live exclusive-lock handle,
//! and fsync a monotonic epoch before it may issue opaque receipt tokens.

const UNSUPPORTED: i64 = -1;

macro_rules! fail_closed {
    ($name:ident($($arg:ident: $ty:ty),*)) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name($($arg: $ty),*) -> i64 {
            $(let _ = $arg;)*
            UNSUPPORTED
        }
    };
}

fail_closed!(rt_cache_host_authenticate_peer_v1(root: i64, transport_peer: i64));
fail_closed!(rt_cache_host_acquire_exclusive_lock_v1(root: i64, peer: i64));
fail_closed!(rt_cache_host_boot_identity_v1(lock: i64));
fail_closed!(rt_cache_host_advance_writer_epoch_v1(lock: i64, boot: i64));
fail_closed!(rt_cache_host_publish_readiness_v1(lock: i64, epoch: i64, nonce: *const u8, nonce_len: i64));
fail_closed!(rt_cache_host_validate_readiness_v1(peer: i64, readiness: i64, nonce: *const u8, nonce_len: i64, epoch: i64));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsupported_provider_never_issues_or_validates_authority() {
        let nonce = b"nonce";
        unsafe {
            assert_eq!(rt_cache_host_authenticate_peer_v1(1, 2), UNSUPPORTED);
            assert_eq!(rt_cache_host_acquire_exclusive_lock_v1(1, 2), UNSUPPORTED);
            assert_eq!(rt_cache_host_boot_identity_v1(1), UNSUPPORTED);
            assert_eq!(rt_cache_host_advance_writer_epoch_v1(1, 2), UNSUPPORTED);
            assert_eq!(
                rt_cache_host_publish_readiness_v1(1, 2, nonce.as_ptr(), nonce.len() as i64),
                UNSUPPORTED
            );
            assert_eq!(
                rt_cache_host_validate_readiness_v1(1, 2, nonce.as_ptr(), nonce.len() as i64, 3),
                UNSUPPORTED
            );
        }
    }
}
