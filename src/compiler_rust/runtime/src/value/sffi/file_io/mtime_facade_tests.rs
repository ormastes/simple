//! Actual managed-path and filesystem tests for the two legacy mtime exports.
use super::*;
use crate::value::collections::{rt_array_free, rt_array_new, rt_string_free, rt_string_new};
use crate::value::RuntimeValue;
use std::fs::{File, FileTimes};
use std::time::{Duration, SystemTime};

fn managed(bytes: &[u8]) -> RuntimeValue {
    rt_string_new(bytes.as_ptr(), bytes.len() as u64)
}

fn native_mtime(path: &Path) -> i64 {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        std::fs::metadata(path).map(|metadata| metadata.mtime()).unwrap_or(-1)
    }
    #[cfg(windows)]
    {
        use std::os::windows::ffi::OsStrExt;
        let wide: Vec<u16> = path.as_os_str().encode_wide().chain(Some(0)).collect();
        let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
        let status = unsafe { libc::wstat(wide.as_ptr(), metadata.as_mut_ptr()) };
        if status != 0 { -1 } else { unsafe { metadata.assume_init().st_mtime as i64 } }
    }
}

fn assert_both(path: &Path, expected: i64) {
    let text = managed(path.to_str().unwrap().as_bytes());
    assert_eq!(rt_file_modified(text), expected);
    assert_eq!(rt_file_modified_time(text), expected);
    rt_string_free(text);
}

fn set_modified(file: &File, time: SystemTime) {
    file.set_times(FileTimes::new().set_modified(time)).unwrap();
}

#[test]
fn mtime_facade_known_fractional_timestamp_and_unicode_path() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("mtime-한글-😀.txt");
    let file = File::create(&path).unwrap();
    set_modified(&file, UNIX_EPOCH + Duration::new(1_600_000_123, 875_000_000));
    assert_eq!(native_mtime(&path), 1_600_000_123);
    assert_both(&path, 1_600_000_123);
}

#[test]
fn mtime_facade_epoch_zero_and_failure_keep_stat_policy_distinct() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("epoch-zero.txt");
    let file = File::create(&path).unwrap();
    set_modified(&file, UNIX_EPOCH);
    #[cfg(unix)]
    assert_eq!(native_mtime(&path), 0);
    // Windows uses the actual CRT oracle, including its local-year boundary.
    assert_both(&path, native_mtime(&path));
    let missing = dir.path().join("missing.txt");
    assert_both(&missing, -1);
    let raw = missing.to_str().unwrap();
    assert_eq!(unsafe { rt_file_stat(raw.as_ptr(), raw.len() as u64) }, 0);
}

#[test]
fn mtime_facade_pre_epoch_fractional_values_match_native_policy() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pre-epoch.txt");
    let file = File::create(&path).unwrap();
    for (before, unix_expected) in [(Duration::from_millis(500), -1),
                                    (Duration::from_secs(1), -1),
                                    (Duration::from_millis(1500), -2)] {
        set_modified(&file, UNIX_EPOCH - before);
        let expected = native_mtime(&path);
        #[cfg(unix)]
        assert_eq!(expected, unix_expected);
        #[cfg(windows)]
        let _ = unix_expected;
        assert_both(&path, expected);
        let raw = path.to_str().unwrap();
        assert_eq!(unsafe { rt_file_stat(raw.as_ptr(), raw.len() as u64) }, 0);
    }
}

#[test]
fn mtime_facade_counted_path_bounds_nul_and_utf8_validation() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("nul-prefix.txt");
    File::create(&path).unwrap();
    let expected = native_mtime(&path);
    let mut padded = path.to_str().unwrap().as_bytes().to_vec();
    padded.push(0);
    padded.resize(4095, b'x');
    let text = managed(&padded);
    assert_eq!(rt_file_modified(text), expected);
    assert_eq!(rt_file_modified_time(text), expected);
    rt_string_free(text);
    padded.push(b'x');
    let oversized = managed(&padded);
    assert_eq!(rt_file_modified(oversized), -1);
    assert_eq!(rt_file_modified_time(oversized), -1);
    rt_string_free(oversized);
    for bytes in [&b""[..], &[0xff, 0xff][..]] {
        let invalid = managed(bytes);
        assert_eq!(rt_file_modified(invalid), -1);
        assert_eq!(rt_file_modified_time(invalid), -1);
        rt_string_free(invalid);
    }
}

#[test]
fn mtime_facade_directories_and_links_keep_native_metadata_behavior() {
    let dir = tempfile::tempdir().unwrap();
    assert_both(dir.path(), native_mtime(dir.path()));
    let file_path = dir.path().join("file.txt");
    File::create(&file_path).unwrap();
    assert_both(&file_path.join("child"), -1);
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let link = dir.path().join("live-link");
        symlink(&file_path, &link).unwrap();
        assert_both(&link, native_mtime(&file_path));
        let dangling = dir.path().join("dangling-link");
        symlink(dir.path().join("absent"), &dangling).unwrap();
        assert_both(&dangling, -1);
    }
    // Windows reparse/symlink fixture privilege is a separate unrun boundary.
}

#[test]
fn mtime_facade_invalid_values_and_registry_owned_copy() {
    let array = rt_array_new(0);
    for value in [RuntimeValue::NIL, RuntimeValue::from_int(7),
                  RuntimeValue::from_bool(false), array] {
        assert_eq!(rt_file_modified(value), -1);
        assert_eq!(rt_file_modified_time(value), -1);
    }
    rt_array_free(array);
    let text = managed(b"copied managed path");
    let mut copied = [0u8; 4096];
    let len = file_mtime_path_copy(text, &mut copied).unwrap();
    rt_string_free(text);
    assert_eq!(&copied[..len], b"copied managed path");
    assert_eq!(rt_file_modified(text), -1);
    assert_eq!(rt_file_modified_time(text), -1);
}
