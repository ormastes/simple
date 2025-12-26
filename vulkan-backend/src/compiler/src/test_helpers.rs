/// Shared test utilities for compiler crate
#[cfg(test)]
use std::fs;
#[cfg(test)]
use tempfile::TempDir;

/// Create a temporary test project directory with src/ subdirectory
#[cfg(test)]
pub fn create_test_project() -> TempDir {
    let dir = TempDir::new().unwrap();
    let src = dir.path().join("src");
    fs::create_dir_all(&src).unwrap();
    dir
}
