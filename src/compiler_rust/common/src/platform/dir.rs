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

/// Walk a directory tree recursively, returning all file paths.
pub fn walk(path: impl AsRef<Path>) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    walk_recursive(path.as_ref(), &mut files)?;
    Ok(files)
}

fn walk_recursive(dir: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                walk_recursive(&path, files)?;
            } else {
                files.push(path);
            }
        }
    }
    Ok(())
}
