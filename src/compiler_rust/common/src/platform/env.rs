//! Cross-platform environment access for the compiler.

use std::path::PathBuf;

/// Get an environment variable value.
pub fn get(name: &str) -> Option<String> {
    std::env::var(name).ok()
}

/// Set an environment variable.
pub fn set(name: &str, value: &str) {
    std::env::set_var(name, value);
}

/// Get the current working directory.
pub fn cwd() -> std::io::Result<PathBuf> {
    std::env::current_dir()
}

/// Get the user's home directory.
pub fn home() -> Option<PathBuf> {
    std::env::var("HOME")
        .or_else(|_| std::env::var("USERPROFILE"))
        .ok()
        .map(PathBuf::from)
}

/// Get the system temporary directory.
pub fn temp() -> PathBuf {
    std::env::temp_dir()
}
