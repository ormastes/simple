//! Cross-platform filesystem operations for the compiler.

use std::io;
use std::path::Path;

/// Read a text file to string, returning an io::Error on failure.
pub fn read_text(path: impl AsRef<Path>) -> io::Result<String> {
    std::fs::read_to_string(path)
}

/// Write text to a file, creating it if it doesn't exist.
pub fn write_text(path: impl AsRef<Path>, content: &str) -> io::Result<()> {
    std::fs::write(path, content)
}

/// Check if a file or directory exists.
pub fn exists(path: impl AsRef<Path>) -> bool {
    path.as_ref().exists()
}

/// Check if a path is a file.
pub fn is_file(path: impl AsRef<Path>) -> bool {
    path.as_ref().is_file()
}

/// Check if a path is a directory.
pub fn is_dir(path: impl AsRef<Path>) -> bool {
    path.as_ref().is_dir()
}

/// Get the file size in bytes.
pub fn file_size(path: impl AsRef<Path>) -> io::Result<u64> {
    Ok(std::fs::metadata(path)?.len())
}
