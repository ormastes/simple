//! Cross-platform directory operations for the compiler.

use std::io;
use std::path::{Path, PathBuf};

/// List entries in a directory.
pub fn list(path: impl AsRef<Path>) -> io::Result<Vec<PathBuf>> {
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(path)? {
        entries.push(entry?.path());
    }
    Ok(entries)
}

/// Create a directory (single level).
pub fn create(path: impl AsRef<Path>) -> io::Result<()> {
    std::fs::create_dir(path)
}

/// Create a directory and all parent directories.
pub fn create_all(path: impl AsRef<Path>) -> io::Result<()> {
    std::fs::create_dir_all(path)
}

/// Check if a directory exists.
pub fn exists(path: impl AsRef<Path>) -> bool {
    path.as_ref().is_dir()
}

/// Walk a directory tree iteratively, returning all file paths.
/// Uses an explicit stack to avoid stack overflow on deep directory trees (Windows default stack is 1 MB).
pub fn walk(path: impl AsRef<Path>) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    let mut stack = vec![path.as_ref().to_path_buf()];
    while let Some(dir) = stack.pop() {
        if dir.is_dir() {
            for entry in std::fs::read_dir(&dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                } else {
                    files.push(path);
                }
            }
        }
    }
    Ok(files)
}
