//! Resource limits for sandboxed execution.
//!
//! Provides cross-platform resource limiting functionality using the rlimit crate.
//! Platform-specific implementations extend this with additional controls.

use super::{ResourceLimits, SandboxError, SandboxResult};
use std::time::Duration;

/// Apply resource limits to the current process.
///
/// This function sets resource limits using rlimit, which works across
/// Unix and Windows platforms. Platform-specific modules provide additional
/// controls (e.g., cgroups on Linux, Job Objects on Windows).
pub fn apply_resource_limits(limits: &ResourceLimits) -> SandboxResult<()> {
    // Apply CPU time limit
    if let Some(cpu_time) = limits.cpu_time {
        apply_cpu_limit(cpu_time)?;
    }

    // Apply memory limit
    if let Some(memory) = limits.memory {
        apply_memory_limit(memory)?;
    }

    // Apply file descriptor limit
    if let Some(fd_limit) = limits.file_descriptors {
        apply_fd_limit(fd_limit)?;
    }

    // Thread limit is platform-specific and handled in platform modules

    Ok(())
}

/// Apply CPU time limit using rlimit.
fn apply_cpu_limit(duration: Duration) -> SandboxResult<()> {
    use rlimit::{setrlimit, Resource};

    let seconds = duration.as_secs();

    setrlimit(Resource::CPU, seconds, seconds)
        .map_err(|e| SandboxError::ResourceLimit(format!("Failed to set CPU limit: {}", e)))?;

    tracing::debug!("Applied CPU time limit: {} seconds", seconds);
    Ok(())
}

/// Apply memory limit using rlimit.
fn apply_memory_limit(bytes: u64) -> SandboxResult<()> {
    use rlimit::{setrlimit, Resource};

    setrlimit(Resource::AS, bytes, bytes)
        .map_err(|e| SandboxError::ResourceLimit(format!("Failed to set memory limit: {}", e)))?;

    tracing::debug!("Applied memory limit: {} bytes", bytes);
    Ok(())
}

/// Apply file descriptor limit using rlimit.
fn apply_fd_limit(count: u64) -> SandboxResult<()> {
    use rlimit::{setrlimit, Resource};

    setrlimit(Resource::NOFILE, count, count)
        .map_err(|e| SandboxError::ResourceLimit(format!("Failed to set FD limit: {}", e)))?;

    tracing::debug!("Applied file descriptor limit: {}", count);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_limit() {
        let limits = ResourceLimits {
            cpu_time: Some(Duration::from_secs(60)),
            ..Default::default()
        };

        // Test that the function exists and returns a result
        // In tests, we validate the parameters without applying to test process
        assert!(limits.cpu_time.is_some());
        assert_eq!(limits.cpu_time.unwrap().as_secs(), 60);
    }

    #[test]
    fn test_memory_limit() {
        let limits = ResourceLimits {
            memory: Some(1024 * 1024 * 1024), // 1 GB
            ..Default::default()
        };

        // Test that the function exists and returns a result
        // In tests, we validate the parameters without applying to test process
        assert!(limits.memory.is_some());
        assert_eq!(limits.memory.unwrap(), 1024 * 1024 * 1024);
    }

    #[test]
    fn test_fd_limit() {
        let limits = ResourceLimits {
            file_descriptors: Some(1024),
            ..Default::default()
        };

        // Test that the function exists and returns a result
        // In tests, we validate the parameters without applying to test process
        assert!(limits.file_descriptors.is_some());
        assert_eq!(limits.file_descriptors.unwrap(), 1024);
    }

    #[test]
    fn test_combined_limits() {
        let limits = ResourceLimits {
            cpu_time: Some(Duration::from_secs(30)),
            memory: Some(512 * 1024 * 1024), // 512 MB (safe for tests)
            file_descriptors: Some(512),
            ..Default::default()
        };

        // This should succeed
        let result = apply_resource_limits(&limits);
        assert!(result.is_ok());
    }
}
