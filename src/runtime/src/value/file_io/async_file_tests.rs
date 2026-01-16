//! Tests for async file I/O functionality

use super::{
    native_async_file_create, native_async_file_get_state, native_async_file_is_ready, native_async_file_start_loading,
    native_async_file_wait, FileLoadState,
};
use crate::value::{rt_string_new, RuntimeValue};
use std::fs::File;
use std::io::Write;

fn create_test_file(path: &str, content: &str) -> std::io::Result<()> {
    let mut file = File::create(path)?;
    file.write_all(content.as_bytes())?;
    Ok(())
}

#[test]
fn test_async_file_create() {
    // Create a test file
    let test_path = "/tmp/test_async_create.txt";
    create_test_file(test_path, "Hello, async file!").unwrap();

    // Create RuntimeValue from string
    let path_value = rt_string_new(test_path.as_ptr(), test_path.len() as u64);

    // Create async file handle
    let handle_id = native_async_file_create(path_value, libc::O_RDONLY, 0);

    // Should return a valid handle ID
    assert!(handle_id > 0);

    // Clean up
    std::fs::remove_file(test_path).ok();
}

#[test]
fn test_async_file_loading_lifecycle() {
    // Create a test file
    let test_path = "/tmp/test_async_lifecycle.txt";
    let test_content = "Async file loading test content";
    create_test_file(test_path, test_content).unwrap();

    // Create handle
    let path_value = rt_string_new(test_path.as_ptr(), test_path.len() as u64);
    let handle_id = native_async_file_create(path_value, libc::O_RDONLY, 0);
    assert!(handle_id > 0);

    // Initial state should be Pending
    assert_eq!(native_async_file_get_state(handle_id), FileLoadState::Pending as i32);
    assert_eq!(native_async_file_is_ready(handle_id), 0);

    // Start loading
    native_async_file_start_loading(handle_id);

    // Wait for completion
    let result = native_async_file_wait(handle_id);

    // Should get a valid pointer
    assert!(result.is_int());
    let ptr = result.as_int();
    assert!(ptr != 0);

    // Should be ready now
    assert_eq!(native_async_file_is_ready(handle_id), 1);
    assert_eq!(native_async_file_get_state(handle_id), FileLoadState::Ready as i32);

    // Clean up
    std::fs::remove_file(test_path).ok();
}

#[test]
fn test_async_file_invalid_path() {
    // Try to load a non-existent file
    let bad_path = "/tmp/nonexistent_file_12345.txt";
    let path_value = rt_string_new(bad_path.as_ptr(), bad_path.len() as u64);

    let handle_id = native_async_file_create(path_value, libc::O_RDONLY, 0);
    assert!(handle_id > 0);

    // Start loading
    native_async_file_start_loading(handle_id);

    // Wait - should fail
    let result = native_async_file_wait(handle_id);

    // Should return 0 on error
    assert_eq!(result.as_int(), 0);

    // State should be Failed
    assert_eq!(native_async_file_get_state(handle_id), FileLoadState::Failed as i32);
}

#[test]
fn test_async_file_invalid_handle() {
    // Try to use an invalid handle ID
    let invalid_handle = 99999;

    // Should return 0 for invalid handle
    assert_eq!(native_async_file_is_ready(invalid_handle), 0);
    assert_eq!(
        native_async_file_get_state(invalid_handle),
        FileLoadState::Failed as i32
    );

    let result = native_async_file_wait(invalid_handle);
    assert_eq!(result.as_int(), 0);
}

#[test]
fn test_async_file_multiple_handles() {
    // Create multiple test files
    let path1 = "/tmp/test_async_multi1.txt";
    let path2 = "/tmp/test_async_multi2.txt";

    create_test_file(path1, "File 1 content").unwrap();
    create_test_file(path2, "File 2 content").unwrap();

    // Create two handles
    let pv1 = rt_string_new(path1.as_ptr(), path1.len() as u64);
    let pv2 = rt_string_new(path2.as_ptr(), path2.len() as u64);

    let handle1 = native_async_file_create(pv1, libc::O_RDONLY, 0);
    let handle2 = native_async_file_create(pv2, libc::O_RDONLY, 0);

    assert!(handle1 > 0);
    assert!(handle2 > 0);
    assert_ne!(handle1, handle2);

    // Start both
    native_async_file_start_loading(handle1);
    native_async_file_start_loading(handle2);

    // Wait for both
    let result1 = native_async_file_wait(handle1);
    let result2 = native_async_file_wait(handle2);

    // Both should succeed
    assert!(result1.as_int() != 0);
    assert!(result2.as_int() != 0);

    // Clean up
    std::fs::remove_file(path1).ok();
    std::fs::remove_file(path2).ok();
}

#[test]
fn test_async_file_with_prefault() {
    // Create a larger test file
    let test_path = "/tmp/test_async_prefault.txt";
    let content = "x".repeat(4096); // 4KB file
    create_test_file(test_path, &content).unwrap();

    // Create handle with prefault enabled
    let path_value = rt_string_new(test_path.as_ptr(), test_path.len() as u64);
    let handle_id = native_async_file_create(path_value, libc::O_RDONLY, 1);

    native_async_file_start_loading(handle_id);
    let result = native_async_file_wait(handle_id);

    // Should still succeed with prefault
    assert!(result.as_int() != 0);
    assert_eq!(native_async_file_is_ready(handle_id), 1);

    // Clean up
    std::fs::remove_file(test_path).ok();
}

#[test]
fn test_async_file_string_extraction_failure() {
    // Pass a non-string RuntimeValue
    let not_a_string = RuntimeValue::from_int(42);

    let handle_id = native_async_file_create(not_a_string, libc::O_RDONLY, 0);

    // Should return 0 for invalid input
    assert_eq!(handle_id, 0);
}
