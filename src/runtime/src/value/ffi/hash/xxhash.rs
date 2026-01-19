//! XXHash function FFI.
//!
//! Provides fast non-cryptographic hashing functionality using XXH3.
//! XXHash is extremely fast and suitable for hash tables, checksums, and non-security applications.
//!
//! **Note:** XXHash is NOT cryptographically secure. Use SHA256 for security purposes.

use std::collections::HashMap;
use std::sync::Mutex;
use xxhash_rust::xxh3::Xxh3;

lazy_static::lazy_static! {
    static ref XXHASH_MAP: Mutex<HashMap<i64, Xxh3>> = Mutex::new(HashMap::new());
}

static mut XXHASH_COUNTER: i64 = 1;

/// Create new XXHash hasher
#[no_mangle]
pub extern "C" fn rt_xxhash_new() -> i64 {
    unsafe {
        let handle = XXHASH_COUNTER;
        XXHASH_COUNTER += 1;
        let hasher = Xxh3::new();
        XXHASH_MAP.lock().unwrap().insert(handle, hasher);
        handle
    }
}

/// Create new XXHash hasher with seed
#[no_mangle]
pub extern "C" fn rt_xxhash_new_with_seed(seed: u64) -> i64 {
    unsafe {
        let handle = XXHASH_COUNTER;
        XXHASH_COUNTER += 1;
        let hasher = Xxh3::with_seed(seed);
        XXHASH_MAP.lock().unwrap().insert(handle, hasher);
        handle
    }
}

/// Write bytes to XXHash hasher
///
/// # Safety
/// data_ptr must be valid for data_len bytes or null
#[no_mangle]
pub unsafe extern "C" fn rt_xxhash_write(handle: i64, data_ptr: *const u8, data_len: u64) {
    if data_ptr.is_null() {
        return;
    }
    let mut map = XXHASH_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
        hasher.update(data);
    }
}

/// Finalize XXHash and get hash value
#[no_mangle]
pub extern "C" fn rt_xxhash_finish(handle: i64) -> u64 {
    let mut map = XXHASH_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        hasher.digest()
    } else {
        0
    }
}

/// Reset XXHash hasher
#[no_mangle]
pub extern "C" fn rt_xxhash_reset(handle: i64) {
    let mut map = XXHASH_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        hasher.reset();
    }
}

/// Free XXHash hasher
#[no_mangle]
pub extern "C" fn rt_xxhash_free(handle: i64) {
    XXHASH_MAP.lock().unwrap().remove(&handle);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_xxhash_basic() {
        let handle = rt_xxhash_new();
        assert!(handle > 0);

        // Hash "hello"
        let data = b"hello";
        unsafe {
            rt_xxhash_write(handle, data.as_ptr(), data.len() as u64);
        }

        let hash = rt_xxhash_finish(handle);
        // XXHash of "hello" (specific value may vary by implementation)
        assert_ne!(hash, 0);
    }

    #[test]
    fn test_xxhash_empty_string() {
        let handle = rt_xxhash_new();

        let hash = rt_xxhash_finish(handle);
        // Empty string has a deterministic hash
        assert_ne!(hash, 0);
    }

    #[test]
    fn test_xxhash_deterministic() {
        // Same input should produce same hash
        let handle1 = rt_xxhash_new();
        let handle2 = rt_xxhash_new();

        unsafe {
            rt_xxhash_write(handle1, b"test".as_ptr(), 4);
            rt_xxhash_write(handle2, b"test".as_ptr(), 4);
        }

        let hash1 = rt_xxhash_finish(handle1);
        let hash2 = rt_xxhash_finish(handle2);

        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_xxhash_different_inputs() {
        let handle1 = rt_xxhash_new();
        let handle2 = rt_xxhash_new();

        unsafe {
            rt_xxhash_write(handle1, b"hello".as_ptr(), 5);
            rt_xxhash_write(handle2, b"world".as_ptr(), 5);
        }

        let hash1 = rt_xxhash_finish(handle1);
        let hash2 = rt_xxhash_finish(handle2);

        // Different inputs should (almost certainly) produce different hashes
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_xxhash_multiple_writes() {
        let handle = rt_xxhash_new();

        // Write "hel" then "lo"
        unsafe {
            rt_xxhash_write(handle, b"hel".as_ptr(), 3);
            rt_xxhash_write(handle, b"lo".as_ptr(), 2);
        }

        let hash1 = rt_xxhash_finish(handle);

        // Compare with hashing "hello" at once
        let handle2 = rt_xxhash_new();
        unsafe {
            rt_xxhash_write(handle2, b"hello".as_ptr(), 5);
        }
        let hash2 = rt_xxhash_finish(handle2);

        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_xxhash_reset() {
        let handle = rt_xxhash_new();

        // Hash something
        unsafe {
            rt_xxhash_write(handle, b"wrong".as_ptr(), 5);
        }

        // Reset and hash the correct data
        rt_xxhash_reset(handle);
        unsafe {
            rt_xxhash_write(handle, b"hello".as_ptr(), 5);
        }

        let hash = rt_xxhash_finish(handle);

        // Compare with fresh hasher
        let handle2 = rt_xxhash_new();
        unsafe {
            rt_xxhash_write(handle2, b"hello".as_ptr(), 5);
        }
        let hash2 = rt_xxhash_finish(handle2);

        assert_eq!(hash, hash2);
    }

    #[test]
    fn test_xxhash_with_seed() {
        let seed = 12345u64;
        let handle1 = rt_xxhash_new_with_seed(seed);
        let handle2 = rt_xxhash_new_with_seed(seed);

        unsafe {
            rt_xxhash_write(handle1, b"test".as_ptr(), 4);
            rt_xxhash_write(handle2, b"test".as_ptr(), 4);
        }

        let hash1 = rt_xxhash_finish(handle1);
        let hash2 = rt_xxhash_finish(handle2);

        // Same seed and input should produce same hash
        assert_eq!(hash1, hash2);

        // Different seed should produce different hash
        let handle3 = rt_xxhash_new_with_seed(54321);
        unsafe {
            rt_xxhash_write(handle3, b"test".as_ptr(), 4);
        }
        let hash3 = rt_xxhash_finish(handle3);
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_xxhash_null_data() {
        let handle = rt_xxhash_new();

        // Writing null data should be safe
        unsafe {
            rt_xxhash_write(handle, std::ptr::null(), 100);
        }

        let hash = rt_xxhash_finish(handle);

        // Should get empty string hash
        let handle2 = rt_xxhash_new();
        let hash2 = rt_xxhash_finish(handle2);

        assert_eq!(hash, hash2);
    }

    #[test]
    fn test_xxhash_invalid_handle() {
        // Finish with invalid handle
        let hash = rt_xxhash_finish(999999);
        assert_eq!(hash, 0);

        // Reset invalid handle (should not crash)
        rt_xxhash_reset(999999);

        // Free invalid handle (should not crash)
        rt_xxhash_free(999999);
    }

    #[test]
    fn test_xxhash_double_free() {
        let handle = rt_xxhash_new();
        rt_xxhash_free(handle);
        // Double free should be safe
        rt_xxhash_free(handle);
    }

    #[test]
    fn test_xxhash_long_input() {
        let handle = rt_xxhash_new();

        // Hash a longer input
        let data = b"The quick brown fox jumps over the lazy dog";
        unsafe {
            rt_xxhash_write(handle, data.as_ptr(), data.len() as u64);
        }

        let hash = rt_xxhash_finish(handle);
        assert_ne!(hash, 0);

        // Verify consistency
        let handle2 = rt_xxhash_new();
        unsafe {
            rt_xxhash_write(handle2, data.as_ptr(), data.len() as u64);
        }
        let hash2 = rt_xxhash_finish(handle2);
        assert_eq!(hash, hash2);
    }

    #[test]
    fn test_xxhash_avalanche() {
        // Small changes in input should produce very different hashes
        let handle1 = rt_xxhash_new();
        let handle2 = rt_xxhash_new();

        unsafe {
            rt_xxhash_write(handle1, b"test1".as_ptr(), 5);
            rt_xxhash_write(handle2, b"test2".as_ptr(), 5);
        }

        let hash1 = rt_xxhash_finish(handle1);
        let hash2 = rt_xxhash_finish(handle2);

        // One bit difference in input should cause significant difference in output
        assert_ne!(hash1, hash2);

        // Count differing bits (should be roughly 50% for good hash function)
        let xor = hash1 ^ hash2;
        let bit_diff = xor.count_ones();
        assert!(
            bit_diff > 10,
            "Hash avalanche effect too weak: only {} bits differ",
            bit_diff
        );
    }
}
