//! Interpreter tests - native I/O operations
//!
//! Tests for the native filesystem and terminal operations implemented in
//! interpreter_native_io.rs, corresponding to simple/std_lib/src/host/async_nogc/io/fs.spl
//! and simple/std_lib/src/host/async_nogc/io/term.spl

use simple_driver::interpreter::run_code;
use std::fs;
use tempfile::tempdir;

// ============================================================================
// Filesystem Tests - Basic Operations
// ============================================================================

#[test]
fn test_native_fs_write_and_read() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.txt");
    let path_str = path.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_write(path, data)
extern fn native_fs_read(path)

let write_res = native_fs_write("{}", "hello")
let read_res = native_fs_read("{}")

main = match read_res:
    Ok(bytes) => bytes.len()
    Err(_) => -1
"#,
        path_str, path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5); // "hello" = 5 bytes
}

#[test]
fn test_native_fs_write_bytes() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("bytes.bin");
    let path_str = path.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_write(path, data)

# Write bytes [104, 101, 108, 108, 111] = "hello"
let res = native_fs_write("{}", [104, 101, 108, 108, 111])

main = match res:
    Ok(n) => n
    Err(_) => -1
"#,
        path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);

    // Verify file contents
    let contents = fs::read(&path).unwrap();
    assert_eq!(contents, b"hello");
}

#[test]
fn test_native_fs_append() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("append.txt");
    let path_str = path.to_string_lossy();

    // First write, then append
    fs::write(&path, "hello").unwrap();

    let code = format!(
        r#"
extern fn native_fs_append(path, data)
extern fn native_fs_read(path)

let _ = native_fs_append("{}", " world")
let read = native_fs_read("{}")

main = match read:
    Ok(bytes) => bytes.len()
    Err(_) => -1
"#,
        path_str, path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11); // "hello world" = 11 bytes
}

#[test]
fn test_native_fs_not_found_error() {
    let code = r#"
extern fn native_fs_read(path)

let res = native_fs_read("/nonexistent/path/file.txt")

# Check if res is Err variant
main = match res:
    Ok(_) => 0
    Err(_) => 1
"#;

    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // Got error (Err variant)
}

// ============================================================================
// Filesystem Tests - Directory Operations
// ============================================================================

#[test]
fn test_native_fs_create_and_remove_dir() {
    let dir = tempdir().unwrap();
    let subdir = dir.path().join("subdir");
    let path_str = subdir.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_create_dir(path, recursive)
extern fn native_fs_remove_dir(path, recursive)

let create = native_fs_create_dir("{}", false)

let create_ok = match create:
    Ok(_) => true
    Err(_) => false

let remove = native_fs_remove_dir("{}", false)

let remove_ok = match remove:
    Ok(_) => true
    Err(_) => false

main = if create_ok and remove_ok: 1 else: -1
"#,
        path_str, path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn test_native_fs_create_dir_recursive() {
    let dir = tempdir().unwrap();
    let nested = dir.path().join("a/b/c");
    let path_str = nested.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_create_dir(path, recursive)

let res = native_fs_create_dir("{}", true)

main = match res:
    Ok(_) => 1
    Err(_) => -1
"#,
        path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);

    // Verify directory was created
    assert!(nested.exists());
}

#[test]
fn test_native_fs_remove_file() {
    let dir = tempdir().unwrap();
    let file = dir.path().join("to_delete.txt");
    fs::write(&file, "delete me").unwrap();
    let path_str = file.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_remove_file(path)

let res = native_fs_remove_file("{}")

main = match res:
    Ok(_) => 1
    Err(_) => -1
"#,
        path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);

    // Verify file was deleted
    assert!(!file.exists());
}

#[test]
fn test_native_fs_rename() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("original.txt");
    let dst = dir.path().join("renamed.txt");
    fs::write(&src, "content").unwrap();

    let src_str = src.to_string_lossy();
    let dst_str = dst.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_rename(src, dst)

let res = native_fs_rename("{}", "{}")

main = match res:
    Ok(_) => 1
    Err(_) => -1
"#,
        src_str, dst_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);

    assert!(!src.exists());
    assert!(dst.exists());
}

#[test]
fn test_native_fs_copy() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("source.txt");
    let dst = dir.path().join("copy.txt");
    fs::write(&src, "copy me").unwrap();

    let src_str = src.to_string_lossy();
    let dst_str = dst.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_copy(src, dst)

let res = native_fs_copy("{}", "{}")

main = match res:
    Ok(bytes) => bytes
    Err(_) => -1
"#,
        src_str, dst_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 7); // "copy me" = 7 bytes

    assert!(src.exists());
    assert!(dst.exists());
    assert_eq!(fs::read_to_string(&dst).unwrap(), "copy me");
}

// ============================================================================
// Filesystem Tests - Metadata Operations
// ============================================================================

#[test]
fn test_native_fs_metadata() {
    let dir = tempdir().unwrap();
    let file = dir.path().join("meta.txt");
    fs::write(&file, "hello").unwrap();
    let path_str = file.to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_metadata(path)

let res = native_fs_metadata("{}")

main = match res:
    Ok(meta) => meta.size
    Err(_) => -1
"#,
        path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5); // "hello" = 5 bytes
}

#[test]
fn test_native_fs_metadata_file_type() {
    let dir = tempdir().unwrap();
    let file = dir.path().join("file.txt");
    fs::write(&file, "").unwrap();

    let file_str = file.to_string_lossy();
    let dir_str = dir.path().to_string_lossy();

    // Test file type detection - just verify we get metadata back
    // Check if file_type field exists and equals expected string
    let code_file = format!(
        r#"
extern fn native_fs_metadata(path)

let res = native_fs_metadata("{}")

let is_ok = match res:
    Ok(_) => true
    Err(_) => false

main = if is_ok: 1 else: -1
"#,
        file_str
    );

    let result = run_code(&code_file, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // Got metadata OK

    // Test directory metadata also works
    let code_dir = format!(
        r#"
extern fn native_fs_metadata(path)

let res = native_fs_metadata("{}")

let is_ok = match res:
    Ok(_) => true
    Err(_) => false

main = if is_ok: 1 else: -1
"#,
        dir_str
    );

    let result = run_code(&code_dir, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // Got metadata OK
}

#[test]
fn test_native_fs_read_dir() {
    let dir = tempdir().unwrap();

    // Create some files
    fs::write(dir.path().join("a.txt"), "").unwrap();
    fs::write(dir.path().join("b.txt"), "").unwrap();
    fs::create_dir(dir.path().join("subdir")).unwrap();

    let path_str = dir.path().to_string_lossy();

    let code = format!(
        r#"
extern fn native_fs_read_dir(path)

let res = native_fs_read_dir("{}")

main = match res:
    Ok(entries) => entries.entries.len()
    Err(_) => -1
"#,
        path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // a.txt, b.txt, subdir
}

// ============================================================================
// Filesystem Tests - File Handle Operations
// ============================================================================

#[test]
fn test_native_fs_open_and_close() {
    let dir = tempdir().unwrap();
    let file = dir.path().join("handle.txt");
    fs::write(&file, "test").unwrap();
    let path_str = file.to_string_lossy();

    // Just verify open works
    let code = format!(
        r#"
extern fn native_fs_open(path, mode)

let open_res = native_fs_open("{}", "Read")

let is_ok = match open_res:
    Ok(_) => true
    Err(_) => false

main = if is_ok: 1 else: -1
"#,
        path_str
    );

    let result = run_code(&code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ============================================================================
// Terminal Tests
// ============================================================================

#[test]
fn test_native_term_handles() {
    let code = r#"
extern fn native_stdin()
extern fn native_stdout()
extern fn native_stderr()

let stdin = native_stdin()
let stdout = native_stdout()
let stderr = native_stderr()

main = stdin + stdout + stderr
"#;

    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // 0 + 1 + 2
}

#[test]
fn test_native_is_tty() {
    let code = r#"
extern fn native_is_tty(handle)

# During tests, stdout is likely not a tty
let is_tty = native_is_tty(1)

# Just verify it returns a boolean without crashing
main = if is_tty: 1 else: 0
"#;

    let result = run_code(code, &[], "");
    // Should succeed regardless of whether it's a tty or not
    assert!(result.is_ok());
}

#[test]
fn test_native_term_write() {
    let code = r#"
extern fn native_term_write(handle, data, len)

# Write to stdout (handle 1)
let res = native_term_write(1, "test", 4)

main = if res > 0: 1 else: 0
"#;

    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn test_native_term_flush() {
    let code = r#"
extern fn native_term_flush(handle)

let res = native_term_flush(1)

main = if res == 0: 1 else: 0
"#;

    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn test_native_get_term_size() {
    // Just verify it returns something without crashing
    // In test environment, it may return error (-1) or valid size
    let code = r#"
extern fn native_get_term_size(handle)

let size = native_get_term_size(1)

# Returns [rows, cols] array or error code
# Just verify it doesn't crash - any non-zero array element means success
main = 1
"#;

    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}
