//! Simple Package Manager
//!
//! UV-style fast package management for Simple language.
//!
//! ## Features
//! - `simple.toml` manifest parsing
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
