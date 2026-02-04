//! I/O environment tests
//! Tests I/O operations with mocking allowed

use std::fs;
use tempfile::tempdir;

#[test]
fn test_filesystem_operations() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("test.txt");

    // Write test
    fs::write(&path, b"hello").expect("write ok");
    assert!(path.exists(), "File should exist after write");

    // Read test
    let data = fs::read(&path).expect("read ok");
    assert_eq!(data, b"hello", "Content should match");

    // Delete test
    fs::remove_file(&path).expect("remove ok");
    assert!(!path.exists(), "File should not exist after remove");
}

#[test]
fn test_temp_directory_creation() {
    let dir = tempdir().expect("tempdir");
    assert!(dir.path().exists(), "Temp directory should exist");
    assert!(dir.path().is_dir(), "Should be a directory");
}

#[test]
fn test_source_file_io() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("program.spl");

    let content = r#"
fn main() -> int = 42
"#;
    fs::write(&source, content).expect("write ok");

    let read_content = fs::read_to_string(&source).expect("read ok");
    assert!(read_content.contains("fn main()"), "Should contain function");
}
