//! Utility SFFI functions for Simple runtime.
//!
//! - FNV-1a hash: implementation in src/runtime/runtime_hash.c

mod c_sffi {
    extern "C" {
        pub(super) fn rt_fnv_hash(data_ptr: *const u8, data_len: u64) -> u64;
    }
}

#[inline(always)]
pub unsafe fn rt_fnv_hash(data_ptr: *const u8, data_len: u64) -> u64 {
    c_sffi::rt_fnv_hash(data_ptr, data_len)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn test_fnv_hash_basic() {
        unsafe {
            let (ptr, len) = str_to_ptr("Hello");
            let hash = rt_fnv_hash(ptr, len);
            assert_ne!(hash, 0);
            assert_eq!(hash, rt_fnv_hash(ptr, len));
        }
    }

    #[test]
    fn test_fnv_hash_empty() {
        unsafe {
            let (ptr, len) = str_to_ptr("");
            assert_eq!(rt_fnv_hash(ptr, len), 0xcbf29ce484222325);
        }
    }

    #[test]
    fn test_fnv_hash_null() {
        unsafe {
            assert_eq!(rt_fnv_hash(std::ptr::null(), 10), 0);
        }
    }
}
