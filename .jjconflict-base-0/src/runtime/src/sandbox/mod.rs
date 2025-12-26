//! Sandboxed execution for Simple language.
//!
//! Provides two complementary systems:
//! - Runtime Sandboxing: Process isolation with resource limits
//! - Environment Isolation: Dependency isolation per project
//!
//! # Features
//!
//! ## Runtime Sandboxing (#916-919)
//! - Resource limits (CPU, memory, time)
//! - Network isolation (block/allowlist domains)
//! - Filesystem isolation (read/write restrictions)
//!
//! ## Environment Isolation (#920-923)
//! - Virtual environments (per-project dependencies)
//! - Package isolation
//! - Reproducible builds (lock files)

pub mod limits;

#[cfg(target_os = "linux")]
pub mod linux;

#[cfg(target_os = "macos")]
pub mod macos;

#[cfg(target_os = "windows")]
pub mod windows;

use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Duration;

/// Sandbox configuration for runtime execution.
///
/// Provides resource limits, network controls, and filesystem restrictions.
#[derive(Debug, Clone)]
pub struct SandboxConfig {
    /// Resource limits
    pub limits: ResourceLimits,
    /// Network isolation rules
    pub network: NetworkIsolation,
    /// Filesystem access restrictions
    pub filesystem: FilesystemIsolation,
}

/// Resource limits for sandboxed execution (#916).
#[derive(Debug, Clone)]
pub struct ResourceLimits {
    /// Maximum CPU time (seconds), None = unlimited
    pub cpu_time: Option<Duration>,
    /// Maximum memory (bytes), None = unlimited
    pub memory: Option<u64>,
    /// Maximum number of file descriptors, None = unlimited
    pub file_descriptors: Option<u64>,
    /// Maximum number of threads, None = unlimited
    pub threads: Option<u64>,
}

/// Network isolation rules (#917).
#[derive(Debug, Clone)]
pub struct NetworkIsolation {
    /// Network access mode
    pub mode: NetworkMode,
    /// Allowed domains (only used with AllowList mode)
    pub allowed_domains: HashSet<String>,
    /// Blocked domains (only used with BlockList mode)
    pub blocked_domains: HashSet<String>,
}

/// Network access modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetworkMode {
    /// Full network access (no restrictions)
    Full,
    /// No network access at all
    None,
    /// Only allow specific domains
    AllowList,
    /// Block specific domains
    BlockList,
}

/// Filesystem isolation rules (#918).
#[derive(Debug, Clone)]
pub struct FilesystemIsolation {
    /// Filesystem access mode
    pub mode: FilesystemMode,
    /// Directories with read access
    pub read_paths: HashSet<PathBuf>,
    /// Directories with write access
    pub write_paths: HashSet<PathBuf>,
    /// Use virtual overlay filesystem
    pub use_overlay: bool,
}

/// Filesystem access modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FilesystemMode {
    /// Full filesystem access (no restrictions)
    Full,
    /// Read-only access to specified paths
    ReadOnly,
    /// Read-write access to specified paths
    Restricted,
    /// Virtual overlay (copy-on-write)
    Overlay,
}

impl Default for SandboxConfig {
    fn default() -> Self {
        Self {
            limits: ResourceLimits::default(),
            network: NetworkIsolation::default(),
            filesystem: FilesystemIsolation::default(),
        }
    }
}

impl Default for ResourceLimits {
    fn default() -> Self {
        Self {
            cpu_time: None,
            memory: None,
            file_descriptors: None,
            threads: None,
        }
    }
}

impl Default for NetworkIsolation {
    fn default() -> Self {
        Self {
            mode: NetworkMode::Full,
            allowed_domains: HashSet::new(),
            blocked_domains: HashSet::new(),
        }
    }
}

impl Default for FilesystemIsolation {
    fn default() -> Self {
        Self {
            mode: FilesystemMode::Full,
            read_paths: HashSet::new(),
            write_paths: HashSet::new(),
            use_overlay: false,
        }
    }
}

impl SandboxConfig {
    /// Create a new sandbox configuration with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set CPU time limit.
    pub fn with_cpu_time(mut self, duration: Duration) -> Self {
        self.limits.cpu_time = Some(duration);
        self
    }

    /// Set memory limit (in bytes).
    pub fn with_memory(mut self, bytes: u64) -> Self {
        self.limits.memory = Some(bytes);
        self
    }

    /// Set file descriptor limit.
    pub fn with_file_descriptors(mut self, count: u64) -> Self {
        self.limits.file_descriptors = Some(count);
        self
    }

    /// Set thread limit.
    pub fn with_threads(mut self, count: u64) -> Self {
        self.limits.threads = Some(count);
        self
    }

    /// Disable network access.
    pub fn with_no_network(mut self) -> Self {
        self.network.mode = NetworkMode::None;
        self
    }

    /// Enable network allowlist mode.
    pub fn with_network_allowlist(mut self, domains: Vec<String>) -> Self {
        self.network.mode = NetworkMode::AllowList;
        self.network.allowed_domains = domains.into_iter().collect();
        self
    }

    /// Enable network blocklist mode.
    pub fn with_network_blocklist(mut self, domains: Vec<String>) -> Self {
        self.network.mode = NetworkMode::BlockList;
        self.network.blocked_domains = domains.into_iter().collect();
        self
    }

    /// Set read-only paths.
    pub fn with_read_paths(mut self, paths: Vec<PathBuf>) -> Self {
        self.filesystem.mode = FilesystemMode::ReadOnly;
        self.filesystem.read_paths = paths.into_iter().collect();
        self
    }

    /// Set read-write restricted paths.
    pub fn with_restricted_paths(mut self, read: Vec<PathBuf>, write: Vec<PathBuf>) -> Self {
        self.filesystem.mode = FilesystemMode::Restricted;
        self.filesystem.read_paths = read.into_iter().collect();
        self.filesystem.write_paths = write.into_iter().collect();
        self
    }

    /// Enable virtual overlay filesystem.
    pub fn with_overlay(mut self) -> Self {
        self.filesystem.mode = FilesystemMode::Overlay;
        self.filesystem.use_overlay = true;
        self
    }
}

/// Result type for sandbox operations.
pub type SandboxResult<T> = Result<T, SandboxError>;

/// Errors that can occur during sandboxing operations.
#[derive(Debug, thiserror::Error)]
pub enum SandboxError {
    #[error("Failed to set resource limit: {0}")]
    ResourceLimit(String),

    #[error("Failed to apply network isolation: {0}")]
    NetworkIsolation(String),

    #[error("Failed to apply filesystem isolation: {0}")]
    FilesystemIsolation(String),

    #[error("Platform not supported: {0}")]
    UnsupportedPlatform(String),

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Configuration error: {0}")]
    Config(String),
}

// Re-export platform-specific functions
#[cfg(target_os = "linux")]
pub use linux::apply_sandbox;

#[cfg(target_os = "macos")]
pub use macos::apply_sandbox;

#[cfg(target_os = "windows")]
pub use windows::apply_sandbox;

// Fallback for unsupported platforms
#[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
pub fn apply_sandbox(_config: &SandboxConfig) -> SandboxResult<()> {
    Err(SandboxError::UnsupportedPlatform(
        "Sandboxing is only supported on Linux, macOS, and Windows".to_string(),
    ))
}
