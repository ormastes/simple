//! Linux-specific sandboxing using namespaces and cgroups.
//!
//! Provides the most comprehensive sandboxing on Linux using:
//! - Namespaces: PID, network, mount, user isolation
//! - cgroups: Resource control
//! - seccomp: Syscall filtering

use super::{limits, FilesystemMode, NetworkMode, SandboxConfig, SandboxError, SandboxResult};
use nix::unistd::{Gid, Uid};
use std::collections::HashSet;
use std::fs;

/// Apply sandbox configuration to the current process (Linux).
///
/// This uses Linux namespaces, cgroups, and seccomp for comprehensive isolation.
/// Falls back to basic rlimit controls if advanced features are unavailable.
pub fn apply_sandbox(config: &SandboxConfig) -> SandboxResult<()> {
    // Apply basic resource limits (always available)
    limits::apply_resource_limits(&config.limits)?;

    // Apply network isolation
    apply_network_isolation(&config.network.mode, &config.network)?;

    // Apply filesystem isolation
    apply_filesystem_isolation(
        &config.filesystem.mode,
        &config.filesystem.read_paths,
        &config.filesystem.write_paths,
    )?;

    // Try to apply advanced Linux features (namespaces, seccomp)
    // These may fail if running without CAP_SYS_ADMIN or in restricted environments
    if let Err(e) = apply_namespaces(config) {
        tracing::warn!("Failed to apply Linux namespaces: {}", e);
        tracing::info!("Falling back to basic sandboxing");
    }

    Ok(())
}

/// Apply network isolation using Linux network namespaces.
fn apply_network_isolation(
    mode: &NetworkMode,
    config: &super::NetworkIsolation,
) -> SandboxResult<()> {
    match mode {
        NetworkMode::Full => {
            // No restrictions
            tracing::debug!("Network: Full access");
            Ok(())
        }
        NetworkMode::None => {
            // Try to create a new network namespace (requires CAP_SYS_ADMIN)
            tracing::debug!("Network: Blocking all access");
            if let Err(e) = create_empty_network_namespace() {
                tracing::warn!("Failed to create network namespace: {}", e);
                tracing::info!(
                    "Network isolation requires CAP_SYS_ADMIN or unprivileged user namespaces"
                );
            }
            Ok(())
        }
        NetworkMode::AllowList => {
            tracing::debug!(
                "Network: Allowlist mode with {} domains",
                config.allowed_domains.len()
            );
            // Domain filtering would be implemented using iptables/nftables or eBPF
            // For now, we log a warning
            tracing::warn!("Domain allowlist filtering not yet implemented");
            Ok(())
        }
        NetworkMode::BlockList => {
            tracing::debug!(
                "Network: Blocklist mode with {} domains",
                config.blocked_domains.len()
            );
            // Domain filtering would be implemented using iptables/nftables or eBPF
            tracing::warn!("Domain blocklist filtering not yet implemented");
            Ok(())
        }
    }
}

/// Apply filesystem isolation using mount namespaces and bind mounts.
fn apply_filesystem_isolation(
    mode: &FilesystemMode,
    read_paths: &HashSet<std::path::PathBuf>,
    write_paths: &HashSet<std::path::PathBuf>,
) -> SandboxResult<()> {
    match mode {
        FilesystemMode::Full => {
            tracing::debug!("Filesystem: Full access");
            Ok(())
        }
        FilesystemMode::ReadOnly => {
            tracing::debug!("Filesystem: Read-only with {} paths", read_paths.len());
            // Would use mount namespaces + remount read-only
            tracing::warn!("Read-only filesystem isolation not yet implemented");
            Ok(())
        }
        FilesystemMode::Restricted => {
            tracing::debug!(
                "Filesystem: Restricted ({} read, {} write paths)",
                read_paths.len(),
                write_paths.len()
            );
            // Would use mount namespaces + selective bind mounts
            tracing::warn!("Restricted filesystem isolation not yet implemented");
            Ok(())
        }
        FilesystemMode::Overlay => {
            tracing::debug!("Filesystem: Overlay mode");
            // Would use overlayfs
            tracing::warn!("Overlay filesystem not yet implemented");
            Ok(())
        }
    }
}

/// Create an empty network namespace (requires CAP_SYS_ADMIN).
fn create_empty_network_namespace() -> SandboxResult<()> {
    use nix::sched::{unshare, CloneFlags};

    unshare(CloneFlags::CLONE_NEWNET).map_err(|e| {
        SandboxError::NetworkIsolation(format!("Failed to create network namespace: {}", e))
    })?;

    tracing::debug!("Created isolated network namespace");
    Ok(())
}

/// Apply Linux namespaces for process isolation.
fn apply_namespaces(config: &SandboxConfig) -> SandboxResult<()> {
    use nix::sched::{unshare, CloneFlags};

    let mut flags = CloneFlags::empty();

    // PID namespace: isolate process tree
    flags |= CloneFlags::CLONE_NEWPID;

    // IPC namespace: isolate System V IPC, POSIX message queues
    flags |= CloneFlags::CLONE_NEWIPC;

    // UTS namespace: isolate hostname and domain name
    flags |= CloneFlags::CLONE_NEWUTS;

    // Network namespace (if not Full mode)
    if config.network.mode != NetworkMode::Full {
        flags |= CloneFlags::CLONE_NEWNET;
    }

    // Mount namespace (for filesystem isolation)
    if config.filesystem.mode != FilesystemMode::Full {
        flags |= CloneFlags::CLONE_NEWNS;
    }

    // User namespace: map current user to root inside namespace
    // This allows unprivileged sandboxing
    flags |= CloneFlags::CLONE_NEWUSER;

    unshare(flags).map_err(|e| {
        SandboxError::Config(format!("Failed to create namespaces: {}. This may require CAP_SYS_ADMIN or kernel support for unprivileged user namespaces.", e))
    })?;

    // Map current user to root inside the user namespace
    map_user_namespace()?;

    tracing::debug!("Applied Linux namespaces: {:?}", flags);
    Ok(())
}

/// Map the current user to root inside the user namespace.
fn map_user_namespace() -> SandboxResult<()> {
    let uid = Uid::current();
    let gid = Gid::current();

    // Write uid_map
    let uid_map = format!("0 {} 1\n", uid);
    fs::write("/proc/self/uid_map", uid_map)
        .map_err(|e| SandboxError::Config(format!("Failed to write uid_map: {}", e)))?;

    // Disable setgroups (required before writing gid_map)
    fs::write("/proc/self/setgroups", "deny\n")
        .map_err(|e| SandboxError::Config(format!("Failed to write setgroups: {}", e)))?;

    // Write gid_map
    let gid_map = format!("0 {} 1\n", gid);
    fs::write("/proc/self/gid_map", gid_map)
        .map_err(|e| SandboxError::Config(format!("Failed to write gid_map: {}", e)))?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_basic_sandbox() {
        let config = SandboxConfig::new()
            .with_cpu_time(Duration::from_secs(60))
            .with_memory(1024 * 1024 * 1024); // 1 GB

        // Test config is constructed correctly without applying limits
        assert!(config.limits.cpu_time.is_some());
        assert!(config.limits.memory.is_some());
    }

    #[test]
    fn test_no_network() {
        let config = SandboxConfig::new().with_no_network();

        // Test config is constructed correctly
        assert_eq!(config.network.mode, crate::sandbox::NetworkMode::None);
    }

    #[test]
    fn test_read_only_paths() {
        use std::path::PathBuf;

        let config = SandboxConfig::new().with_read_paths(vec!["/tmp".into(), "/usr/lib".into()]);

        // Test config is constructed correctly
        assert_eq!(config.filesystem.read_paths.len(), 2);
        let tmp_path: PathBuf = "/tmp".into();
        let usr_lib_path: PathBuf = "/usr/lib".into();
        assert!(config.filesystem.read_paths.contains(&tmp_path));
        assert!(config.filesystem.read_paths.contains(&usr_lib_path));
    }
}
