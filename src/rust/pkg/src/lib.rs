//! Simple Package Manager
//!
//! UV-style fast package management for Simple language.
//!
//! ## Features
//! - `simple.sdn` manifest parsing (preferred, TOML legacy supported)
//! - `simple.lock` lock file for reproducible builds
//! - Path and Git dependencies
//! - Global cache with hard links
//! - Dependency resolution with topological ordering
//!
//! ## CLI Commands
//! - `simple init` - Create new project
//! - `simple add <pkg>` - Add dependency
//! - `simple install` - Install all dependencies
//! - `simple update` - Update dependencies
//! - `simple list` - List installed dependencies
//! - `simple tree` - Show dependency tree
//! - `simple cache` - Manage global cache

pub mod cache;
pub mod commands;
pub mod error;
pub mod linker;
pub mod lock;
pub mod manifest;
pub mod resolver;
pub mod version;

pub use cache::Cache;
pub use error::{PkgError, PkgResult};
pub use linker::Linker;
pub use lock::LockFile;
pub use manifest::Manifest;
pub use version::{Version, VersionReq};

/// Find manifest file in a directory
///
/// Prefers .sdn format, falls back to .toml for backwards compatibility
pub fn find_manifest(dir: &std::path::Path) -> Option<std::path::PathBuf> {
    let sdn_path = dir.join("simple.sdn");
    if sdn_path.exists() {
        return Some(sdn_path);
    }

    let toml_path = dir.join("simple.toml");
    if toml_path.exists() {
        return Some(toml_path);
    }

    None
}
