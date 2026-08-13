//! File metadata and existence checks.
//!
//! Provides operations for checking file/directory existence and
//! retrieving comprehensive file metadata (type, permissions, size).

use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::UNIX_EPOCH;

/*
 * Failed existence probes are owned by the rt_file_exists facade.  They never
 * count platform syscalls: a facade call can fail before it reaches Path::exists
 * (for example, an invalid byte span), and that failed facade result is still
 * meaningful loader evidence.
 *
 * The state atomically owns accepting and in-flight leases.  Each lease captures
 * a separate monotonic generation before the facade performs Path::exists.
 * end closes accepting, drains leases, and only then snapshots its generation.
 */
const FILE_EXISTS_PROBE_ACCEPTING: u64 = 1 << 63;
const FILE_EXISTS_PROBE_TRANSITION: u64 = 1 << 62;
const FILE_EXISTS_PROBE_LEASE_MASK: u64 = FILE_EXISTS_PROBE_TRANSITION - 1;
const FILE_EXISTS_PROBE_GENERATION_MAX: u64 = 0x7fff_ffff_ffff_ffff;
const FILE_EXISTS_PROBE_TOTAL_MAX: u64 = 0x7fff_ffff;

static FILE_EXISTS_PROBE_STATE: AtomicU64 = AtomicU64::new(0);
static FILE_EXISTS_PROBE_GENERATION: AtomicU64 = AtomicU64::new(0);
static FILE_EXISTS_PROBE_TOTAL: AtomicU64 = AtomicU64::new(0);
static FILE_EXISTS_PROBE_FAILED: AtomicU64 = AtomicU64::new(0);

#[cfg(test)]
static FILE_EXISTS_PROBE_AFTER_ADMIT_HOOK: std::sync::Mutex<
    Option<(std::sync::Arc<std::sync::Barrier>, std::sync::Arc<std::sync::Barrier>)>,
> = std::sync::Mutex::new(None);
#[cfg(test)]
static FILE_EXISTS_PROBE_END_CLOSED_HOOK: std::sync::Mutex<Option<std::sync::Arc<std::sync::Barrier>>> =
    std::sync::Mutex::new(None);

#[cfg(test)]
fn file_exists_probe_after_admit_test_hook(lease: u64) {
    if lease == 0 {
        return;
    }
    let hook = FILE_EXISTS_PROBE_AFTER_ADMIT_HOOK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone();
    if let Some((admitted, release)) = hook {
        admitted.wait();
        release.wait();
    }
}

#[cfg(test)]
fn file_exists_probe_end_closed_test_hook() {
    let hook = FILE_EXISTS_PROBE_END_CLOSED_HOOK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone();
    if let Some(closed) = hook {
        closed.wait();
    }
}

/// Reserve one total slot before a failed slot can be incremented. This makes
/// `failed <= total <= TOTAL_MAX` hold even when records complete concurrently.
fn file_exists_probe_try_add_total() -> bool {
    let mut current = FILE_EXISTS_PROBE_TOTAL.load(Ordering::Relaxed);
    while current < FILE_EXISTS_PROBE_TOTAL_MAX {
        match FILE_EXISTS_PROBE_TOTAL.compare_exchange_weak(
            current,
            current + 1,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            Ok(_) => return true,
            Err(observed) => current = observed,
        }
    }
    false
}

fn file_exists_probe_lease_admit() -> u64 {
    // Disabled source path: one relaxed gate load, without assembly claims.
    let mut state = FILE_EXISTS_PROBE_STATE.load(Ordering::Relaxed);
    if state & FILE_EXISTS_PROBE_ACCEPTING == 0 {
        return 0;
    }

    loop {
        if state & FILE_EXISTS_PROBE_ACCEPTING == 0 {
            return 0;
        }
        if state & FILE_EXISTS_PROBE_LEASE_MASK == FILE_EXISTS_PROBE_LEASE_MASK {
            return 0;
        }
        match FILE_EXISTS_PROBE_STATE.compare_exchange_weak(state, state + 1, Ordering::Acquire, Ordering::Relaxed) {
            Ok(_) => {
                let generation = FILE_EXISTS_PROBE_GENERATION.load(Ordering::Acquire);
                if generation != 0 {
                    return generation;
                }
                FILE_EXISTS_PROBE_STATE.fetch_sub(1, Ordering::Release);
                return 0;
            }
            Err(observed) => state = observed,
        }
    }
}

fn file_exists_probe_record(lease: u64, exists: bool) {
    if lease != 0 && FILE_EXISTS_PROBE_GENERATION.load(Ordering::Acquire) == lease {
        if file_exists_probe_try_add_total() && !exists {
            let mut failed = FILE_EXISTS_PROBE_FAILED.load(Ordering::Relaxed);
            while failed < FILE_EXISTS_PROBE_TOTAL_MAX {
                match FILE_EXISTS_PROBE_FAILED.compare_exchange_weak(
                    failed,
                    failed + 1,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(observed) => failed = observed,
                }
            }
        }
    }
    if lease != 0 {
        FILE_EXISTS_PROBE_STATE.fetch_sub(1, Ordering::Release);
    }
}

/// Begin a failed-existence-probe measurement generation.
///
/// Returns a non-reusable positive generation token, or -1 when another
/// generation is active or draining. Overflow fails closed with -3.
#[no_mangle]
pub extern "C" fn rt_file_exists_probe_begin() -> i64 {
    if FILE_EXISTS_PROBE_STATE
        .compare_exchange(0, FILE_EXISTS_PROBE_TRANSITION, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        return -1;
    }
    let generation = FILE_EXISTS_PROBE_GENERATION.load(Ordering::Acquire);
    if generation >= FILE_EXISTS_PROBE_GENERATION_MAX {
        FILE_EXISTS_PROBE_STATE.store(0, Ordering::Release);
        return -3;
    }
    let generation = generation + 1;
    FILE_EXISTS_PROBE_GENERATION.store(generation, Ordering::Release);
    FILE_EXISTS_PROBE_TOTAL.store(0, Ordering::Relaxed);
    FILE_EXISTS_PROBE_FAILED.store(0, Ordering::Relaxed);
    FILE_EXISTS_PROBE_STATE.store(FILE_EXISTS_PROBE_ACCEPTING, Ordering::Release);
    generation as i64
}

/// Finish a generation and return `(total << 32) | failed`.
///
/// `failed <= total <= 0x7fffffff`, leaving the packed i64 nonnegative.
/// Invalid/stale tokens return -2.
#[no_mangle]
pub extern "C" fn rt_file_exists_probe_end(token: i64) -> i64 {
    if token <= 0
        || token as u64 > FILE_EXISTS_PROBE_GENERATION_MAX
        || FILE_EXISTS_PROBE_GENERATION.load(Ordering::Acquire) != token as u64
    {
        return -2;
    }

    let mut state = FILE_EXISTS_PROBE_STATE.load(Ordering::Acquire);
    loop {
        if state & FILE_EXISTS_PROBE_ACCEPTING == 0
            || FILE_EXISTS_PROBE_GENERATION.load(Ordering::Acquire) != token as u64
        {
            return -2;
        }
        let closing = (state & FILE_EXISTS_PROBE_LEASE_MASK) | FILE_EXISTS_PROBE_TRANSITION;
        match FILE_EXISTS_PROBE_STATE.compare_exchange_weak(state, closing, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => {
                #[cfg(test)]
                file_exists_probe_end_closed_test_hook();
                break;
            }
            Err(observed) => state = observed,
        }
    }

    loop {
        state = FILE_EXISTS_PROBE_STATE.load(Ordering::Acquire);
        if state & FILE_EXISTS_PROBE_LEASE_MASK == 0 {
            break;
        }
        std::hint::spin_loop();
    }

    let total = FILE_EXISTS_PROBE_TOTAL
        .load(Ordering::Acquire)
        .min(FILE_EXISTS_PROBE_TOTAL_MAX);
    let failed = FILE_EXISTS_PROBE_FAILED
        .load(Ordering::Acquire)
        .min(FILE_EXISTS_PROBE_TOTAL_MAX);
    FILE_EXISTS_PROBE_STATE.store(0, Ordering::Release);
    ((total << 32) | failed) as i64
}

#[cfg(test)]
fn file_exists_probe_test_seed_generation(generation: u64) -> i64 {
    if generation > FILE_EXISTS_PROBE_GENERATION_MAX {
        return -3;
    }
    if FILE_EXISTS_PROBE_STATE
        .compare_exchange(0, FILE_EXISTS_PROBE_TRANSITION, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        return -1;
    }
    FILE_EXISTS_PROBE_GENERATION.store(generation, Ordering::Release);
    FILE_EXISTS_PROBE_TOTAL.store(0, Ordering::Relaxed);
    FILE_EXISTS_PROBE_FAILED.store(0, Ordering::Relaxed);
    FILE_EXISTS_PROBE_STATE.store(0, Ordering::Release);
    0
}

#[cfg(test)]
fn file_exists_probe_test_seed_counters(total: u64, failed: u64) -> i64 {
    if total > FILE_EXISTS_PROBE_TOTAL_MAX || failed > total {
        return -3;
    }
    let state = FILE_EXISTS_PROBE_STATE.load(Ordering::Acquire);
    if state & FILE_EXISTS_PROBE_ACCEPTING == 0 || state & FILE_EXISTS_PROBE_LEASE_MASK != 0 {
        return -1;
    }
    FILE_EXISTS_PROBE_TOTAL.store(total, Ordering::Relaxed);
    FILE_EXISTS_PROBE_FAILED.store(failed, Ordering::Relaxed);
    0
}

/// Check if a file or directory exists
#[no_mangle]
pub unsafe extern "C" fn rt_file_exists(path_ptr: *const u8, path_len: u64) -> bool {
    let lease = file_exists_probe_lease_admit();
    #[cfg(test)]
    file_exists_probe_after_admit_test_hook(lease);
    let exists = if path_ptr.is_null() {
        false
    } else {
        let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
        match std::str::from_utf8(path_bytes) {
            Ok(path_str) => Path::new(path_str).exists(),
            Err(_) => false,
        }
    };
    file_exists_probe_record(lease, exists);
    exists
}

/// Check that a path names a regular file without following a final symlink.
#[no_mangle]
pub unsafe extern "C" fn rt_file_is_regular_no_follow(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    std::str::from_utf8(path_bytes)
        .ok()
        .and_then(|path| std::fs::symlink_metadata(path).ok())
        .map(|metadata| metadata.file_type().is_file())
        .unwrap_or(false)
}

/// Check whether a path resolves to a character device.
#[no_mangle]
pub unsafe extern "C" fn rt_file_is_char_device(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let Ok(path) = std::str::from_utf8(path_bytes) else {
        return false;
    };

    #[cfg(unix)]
    {
        use std::os::unix::fs::FileTypeExt;
        std::fs::metadata(path)
            .map(|metadata| metadata.file_type().is_char_device())
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        let _ = path;
        false
    }
}

/// Check if a path exists and is a directory.
#[no_mangle]
pub unsafe extern "C" fn rt_dir_exists(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    match std::str::from_utf8(path_bytes) {
        Ok(path_str) => Path::new(path_str).is_dir(),
        Err(_) => false,
    }
}

/// Get file modification time in seconds since epoch.
#[no_mangle]
pub unsafe extern "C" fn rt_file_stat(path_ptr: *const u8, path_len: u64) -> i64 {
    if path_ptr.is_null() {
        return 0;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return 0,
    };

    std::fs::metadata(Path::new(path_str))
        .and_then(|metadata| metadata.modified())
        .ok()
        .and_then(|modified| modified.duration_since(UNIX_EPOCH).ok())
        .map(|duration| duration.as_secs() as i64)
        .unwrap_or(0)
}

/// Get file metadata as a struct.
/// Returns: [exists, is_file, is_dir, is_readable, is_writable, size].
pub unsafe extern "C" fn rt_file_metadata(
    path_ptr: *const u8,
    path_len: u64,
    out_exists: *mut bool,
    out_is_file: *mut bool,
    out_is_dir: *mut bool,
    out_is_readable: *mut bool,
    out_is_writable: *mut bool,
    out_size: *mut i64,
) {
    // Initialize all outputs to false/0
    if !out_exists.is_null() {
        *out_exists = false;
    }
    if !out_is_file.is_null() {
        *out_is_file = false;
    }
    if !out_is_dir.is_null() {
        *out_is_dir = false;
    }
    if !out_is_readable.is_null() {
        *out_is_readable = false;
    }
    if !out_is_writable.is_null() {
        *out_is_writable = false;
    }
    if !out_size.is_null() {
        *out_size = 0;
    }

    if path_ptr.is_null() {
        return;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };

    let path = Path::new(path_str);

    // Check existence
    if !out_exists.is_null() {
        *out_exists = path.exists();
    }

    if !path.exists() {
        return;
    }

    // Get metadata
    if let Ok(metadata) = std::fs::metadata(path) {
        if !out_is_file.is_null() {
            *out_is_file = metadata.is_file();
        }
        if !out_is_dir.is_null() {
            *out_is_dir = metadata.is_dir();
        }
        if !out_size.is_null() {
            *out_size = metadata.len() as i64;
        }

        // Check permissions (Unix-specific)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = metadata.permissions().mode();

            if !out_is_readable.is_null() {
                *out_is_readable = (mode & 0o400) != 0; // Owner read
            }
            if !out_is_writable.is_null() {
                *out_is_writable = (mode & 0o200) != 0; // Owner write
            }
        }

        // Fallback for non-Unix platforms
        #[cfg(not(unix))]
        {
            if !out_is_readable.is_null() {
                *out_is_readable = !metadata.permissions().readonly();
            }
            if !out_is_writable.is_null() {
                *out_is_writable = !metadata.permissions().readonly();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier, Mutex};

    static FILE_EXISTS_PROBE_TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn file_exists_probe_packs_failed_facade_results_and_rejects_stale_token() {
        let _serial = FILE_EXISTS_PROBE_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        assert_eq!(file_exists_probe_test_seed_generation(0), 0);
        let missing = std::env::temp_dir().join(format!(
            "simple_failed_existence_probe_missing_{}_{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("runtime")
        ));
        let missing = missing.to_string_lossy();
        let _ = std::fs::remove_file(missing.as_ref());

        let token = rt_file_exists_probe_begin();
        assert!(token > 0);
        unsafe {
            assert!(!rt_file_exists(missing.as_ptr(), missing.len() as u64));
            assert!(!rt_file_exists(missing.as_ptr(), missing.len() as u64));
        }
        let packed = rt_file_exists_probe_end(token);
        assert_eq!(packed >> 32, 2);
        assert_eq!(packed & 0xffff_ffff, 2);
        assert_eq!(rt_file_exists_probe_end(token), -2);
    }

    #[test]
    fn file_exists_probe_generation_never_wraps_or_reaccepts_an_old_token() {
        let _serial = FILE_EXISTS_PROBE_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        assert_eq!(
            file_exists_probe_test_seed_generation(FILE_EXISTS_PROBE_GENERATION_MAX - 1),
            0
        );
        let last = rt_file_exists_probe_begin();
        assert_eq!(last as u64, FILE_EXISTS_PROBE_GENERATION_MAX);
        assert_eq!(rt_file_exists_probe_end(last), 0);
        assert_eq!(rt_file_exists_probe_begin(), -3);
        assert_eq!(rt_file_exists_probe_end(last), -2);
        assert_eq!(file_exists_probe_test_seed_generation(0), 0);
    }

    #[test]
    fn file_exists_probe_saturates_total_and_failed_together() {
        let _serial = FILE_EXISTS_PROBE_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        assert_eq!(file_exists_probe_test_seed_generation(0), 0);
        let missing = std::env::temp_dir().join(format!(
            "simple_failed_existence_probe_saturation_{}",
            std::process::id()
        ));
        let missing = missing.to_string_lossy();
        let _ = std::fs::remove_file(missing.as_ref());
        let token = rt_file_exists_probe_begin();
        assert!(token > 0);
        assert_eq!(
            file_exists_probe_test_seed_counters(
                FILE_EXISTS_PROBE_TOTAL_MAX - 1,
                FILE_EXISTS_PROBE_TOTAL_MAX - 1,
            ),
            0
        );
        unsafe {
            assert!(!rt_file_exists(missing.as_ptr(), missing.len() as u64));
            assert!(!rt_file_exists(missing.as_ptr(), missing.len() as u64));
        }
        let packed = rt_file_exists_probe_end(token);
        assert_eq!(packed >> 32, FILE_EXISTS_PROBE_TOTAL_MAX as i64);
        assert_eq!(packed & 0xffff_ffff, FILE_EXISTS_PROBE_TOTAL_MAX as i64);
    }

    #[test]
    fn file_exists_probe_close_drains_pre_end_facade_lease_only() {
        let _serial = FILE_EXISTS_PROBE_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        assert_eq!(file_exists_probe_test_seed_generation(0), 0);
        let missing = std::env::temp_dir().join(format!(
            "simple_failed_existence_probe_lease_{}_{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("runtime")
        ));
        let missing = Arc::new(missing.to_string_lossy().into_owned().into_bytes());
        let _ = std::fs::remove_file(std::str::from_utf8(&missing).unwrap());

        let admitted = Arc::new(Barrier::new(2));
        let release = Arc::new(Barrier::new(2));
        *FILE_EXISTS_PROBE_AFTER_ADMIT_HOOK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) =
            Some((Arc::clone(&admitted), Arc::clone(&release)));

        let token = rt_file_exists_probe_begin();
        assert!(token > 0);
        let worker_path = Arc::clone(&missing);
        let worker = std::thread::spawn(move || unsafe {
            assert!(!rt_file_exists(worker_path.as_ptr(), worker_path.len() as u64));
        });
        admitted.wait();

        let closed = Arc::new(Barrier::new(2));
        *FILE_EXISTS_PROBE_END_CLOSED_HOOK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(Arc::clone(&closed));
        let closer = std::thread::spawn(move || rt_file_exists_probe_end(token));
        closed.wait();

        unsafe {
            assert!(!rt_file_exists(missing.as_ptr(), missing.len() as u64));
        }
        release.wait();
        worker.join().unwrap();
        let packed = closer.join().unwrap();

        *FILE_EXISTS_PROBE_AFTER_ADMIT_HOOK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) = None;
        *FILE_EXISTS_PROBE_END_CLOSED_HOOK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) = None;
        assert_eq!(packed >> 32, 1);
        assert_eq!(packed & 0xffff_ffff, 1);

        let next = rt_file_exists_probe_begin();
        assert!(next > token);
        assert_eq!(rt_file_exists_probe_end(token), -2);
        assert_eq!(rt_file_exists_probe_end(next), 0);
    }

    #[test]
    fn test_file_exists_null_path() {
        let _serial = FILE_EXISTS_PROBE_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        unsafe {
            assert!(!rt_file_exists(std::ptr::null(), 0));
        }
    }

    #[test]
    fn test_file_stat_null_path() {
        unsafe {
            assert_eq!(rt_file_stat(std::ptr::null(), 0), 0);
        }
    }

    #[test]
    fn test_file_is_regular_no_follow() {
        let root = std::env::temp_dir().join(format!("simple_regular_no_follow_{}", std::process::id()));
        let file = root.join("file");
        let missing = root.join("missing");
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(&file, b"ok").unwrap();

        unsafe {
            let file = file.to_string_lossy();
            assert!(rt_file_is_regular_no_follow(file.as_ptr(), file.len() as u64));
            let root_path = root.to_string_lossy();
            assert!(!rt_file_is_regular_no_follow(
                root_path.as_ptr(),
                root_path.len() as u64
            ));
            let missing = missing.to_string_lossy();
            assert!(!rt_file_is_regular_no_follow(missing.as_ptr(), missing.len() as u64));
            assert!(!rt_file_is_regular_no_follow(std::ptr::null(), 0));
        }

        #[cfg(unix)]
        {
            let link = root.join("link");
            std::os::unix::fs::symlink(&file, &link).unwrap();
            let link = link.to_string_lossy();
            unsafe {
                assert!(!rt_file_is_regular_no_follow(link.as_ptr(), link.len() as u64));
            }
        }

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn test_file_stat_existing_path_returns_mtime() {
        let path = std::env::temp_dir().join("simple_runtime_file_stat_mtime_test");
        std::fs::write(&path, b"mtime").unwrap();
        let path_string = path.to_string_lossy();

        unsafe {
            let mtime = rt_file_stat(path_string.as_ptr(), path_string.len() as u64);
            assert!(mtime > 0);
        }

        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn test_file_metadata_null_path() {
        unsafe {
            let mut exists = true;
            rt_file_metadata(
                std::ptr::null(),
                0,
                &mut exists,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            );
            assert!(!exists);
        }
    }
}
