//! Cross-platform path manipulation utilities for the compiler.

use std::path::{Path, PathBuf};

/// Join two path segments.
pub fn join(base: impl AsRef<Path>, part: impl AsRef<Path>) -> PathBuf {
    base.as_ref().join(part)
}

/// Get the absolute path.
pub fn absolute(path: impl AsRef<Path>) -> std::io::Result<PathBuf> {
    std::fs::canonicalize(path)
}

/// Get the parent directory.
pub fn parent(path: impl AsRef<Path>) -> Option<PathBuf> {
    path.as_ref().parent().map(|p| p.to_path_buf())
}

/// Get the file extension (without the dot).
pub fn extension(path: impl AsRef<Path>) -> Option<String> {
    path.as_ref()
        .extension()
        .and_then(|e| e.to_str())
        .map(|s| s.to_string())
}

/// Get the file name (last component).
pub fn file_name(path: impl AsRef<Path>) -> Option<String> {
    path.as_ref()
        .file_name()
        .and_then(|n| n.to_str())
        .map(|s| s.to_string())
}

/// Get the file stem (name without extension).
pub fn stem(path: impl AsRef<Path>) -> Option<String> {
    path.as_ref()
        .file_stem()
        .and_then(|n| n.to_str())
        .map(|s| s.to_string())
}

/// Get the platform-appropriate path separator.
pub fn separator() -> char {
    std::path::MAIN_SEPARATOR
}
