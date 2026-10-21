//! Native Windows environment/cwd ABI controls; independent of the interpreter.
#![cfg(windows)]
use simple_runtime::value::sffi::env_process::{rt_env_get, rt_env_set, rt_env_remove, rt_env_cwd};
use simple_runtime::value::{rt_string_data, rt_string_len, RuntimeValue};
use std::os::windows::ffi::OsStringExt;

fn decode(value: RuntimeValue) -> String {
    assert_ne!(value, RuntimeValue::NIL);
    let bytes = unsafe { std::slice::from_raw_parts(rt_string_data(value), rt_string_len(value) as usize) };
    String::from_utf8(bytes.to_vec()).unwrap()
}

#[test]
fn unicode_environment_and_strict_current_directory() {
    let key = format!("SIMPLE_NATIVE_UTF8_환경_é_{}", std::process::id());
    let value = "값-é-😀";
    unsafe {
        assert!(rt_env_remove(key.as_ptr(), key.len() as u64));
        assert_eq!(rt_env_get(key.as_ptr(), key.len() as u64), RuntimeValue::NIL);
        assert!(rt_env_set(key.as_ptr(), key.len() as u64, b"".as_ptr(), 0));
        assert_eq!(decode(rt_env_get(key.as_ptr(), key.len() as u64)), "");
        assert!(rt_env_set(key.as_ptr(), key.len() as u64, value.as_ptr(), value.len() as u64));
        assert_eq!(decode(rt_env_get(key.as_ptr(), key.len() as u64)), value);
        assert!(rt_env_remove(key.as_ptr(), key.len() as u64));
        assert_eq!(rt_env_get(key.as_ptr(), key.len() as u64), RuntimeValue::NIL);
    }
    let original = std::env::current_dir().unwrap();
    struct Restore(std::path::PathBuf);
    impl Drop for Restore { fn drop(&mut self) { let _ = std::env::set_current_dir(&self.0); } }
    let _restore = Restore(original);
    let root = tempfile::tempdir().unwrap();
    let unicode = root.path().join("환경-é-😀");
    std::fs::create_dir(&unicode).unwrap();
    std::env::set_current_dir(&unicode).unwrap();
    assert_eq!(unsafe { decode(rt_env_cwd()) }, unicode.to_str().unwrap());
    // Windows permits an unpaired UTF-16 surrogate in a filesystem name.
    // The ordinary UTF-8 ABI must report failure rather than replace it.
    let malformed = root.path().join(std::ffi::OsString::from_wide(&[b'x' as u16, 0xD800]));
    std::fs::create_dir(&malformed).unwrap();
    std::env::set_current_dir(&malformed).unwrap();
    assert_eq!(unsafe { rt_env_cwd() }, RuntimeValue::NIL);
    std::env::set_current_dir(&_restore.0).unwrap();
}