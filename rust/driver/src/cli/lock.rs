//! Lock file CLI commands (stubs)
//!
//! The Rust `simple-pkg` crate has been removed. Lock file management
//! is now handled by the Simple app (src/app/lock/main.spl).

use std::path::Path;

/// Generate or update the lock file
pub fn generate_lock(project_dir: &Path) -> i32 {
    eprintln!("Lock file management is handled by the Simple app.");
    eprintln!("Run: simple lock");
    1
}

/// Check if lock file is up-to-date with manifest
pub fn check_lock(project_dir: &Path) -> i32 {
    eprintln!("Lock file management is handled by the Simple app.");
    eprintln!("Run: simple lock --check");
    1
}

/// Install dependencies from lock file
pub fn install_locked(project_dir: &Path) -> i32 {
    eprintln!("Lock file management is handled by the Simple app.");
    eprintln!("Run: simple install --locked");
    1
}

/// Print lock file info
pub fn lock_info(project_dir: &Path) -> i32 {
    eprintln!("Lock file management is handled by the Simple app.");
    eprintln!("Run: simple lock --info");
    1
}
