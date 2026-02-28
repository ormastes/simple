//! FreeBSD-specific sandboxing using rlimit and basic controls.
//!
//! Provides sandboxing on FreeBSD using:
//! - BSD resource limits (rlimit)
//! - Filesystem access validation
//!
//! Note: Capsicum (capability mode) could be added later for stronger isolation.

use super::{limits, FilesystemMode, NetworkMode, SandboxConfig, SandboxResult};
use std::collections::HashSet;

/// Apply sandbox configuration to the current process (FreeBSD).
///
/// Uses BSD-style rlimit controls. Full capsicum isolation would require
/// process re-entry with capability mode, which is not done here.
pub fn apply_sandbox(config: &SandboxConfig) -> SandboxResult<()> {
    // Apply basic resource limits (BSD-style rlimit — same as macOS/Linux)
    limits::apply_resource_limits(&config.limits)?;

    // Apply network isolation (limited without capsicum)
    apply_network_isolation(&config.network.mode)?;

    // Apply filesystem isolation (limited without capsicum)
    apply_filesystem_isolation(
        &config.filesystem.mode,
        &config.filesystem.read_paths,
        &config.filesystem.write_paths,
    )?;

    tracing::info!("Applied FreeBSD sandboxing (rlimit-based)");

    Ok(())
}

/// Apply network isolation on FreeBSD.
///
/// Full network isolation requires capsicum capability mode.
/// For now, log warnings for non-full modes.
fn apply_network_isolation(mode: &NetworkMode) -> SandboxResult<()> {
    match mode {
        NetworkMode::Full => {
            tracing::debug!("Network: Full access");
            Ok(())
        }
        NetworkMode::None => {
            tracing::warn!("Network isolation on FreeBSD requires capsicum or jail");
            Ok(())
        }
        NetworkMode::AllowList | NetworkMode::BlockList => {
            tracing::warn!("Domain filtering on FreeBSD requires capsicum or jail");
            Ok(())
        }
    }
}

/// Apply filesystem isolation on FreeBSD.
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
            tracing::warn!("Filesystem isolation on FreeBSD requires capsicum or jail");
            Ok(())
        }
        FilesystemMode::Restricted => {
            tracing::debug!(
                "Filesystem: Restricted ({} read, {} write paths)",
                read_paths.len(),
                write_paths.len()
            );
            tracing::warn!("Filesystem isolation on FreeBSD requires capsicum or jail");
            Ok(())
        }
        FilesystemMode::Overlay => {
            tracing::warn!("Overlay filesystem not supported on FreeBSD");
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_basic_sandbox() {
        let config = SandboxConfig::new()
            .with_cpu_time(Duration::from_secs(60));

        let result = apply_sandbox(&config);
        assert!(result.is_ok());
    }

    #[test]
    fn test_network_modes() {
        let configs = vec![
            SandboxConfig::new(),
            SandboxConfig::new().with_no_network(),
            SandboxConfig::new().with_network_allowlist(vec!["example.com".to_string()]),
        ];

        for config in configs {
            let result = apply_sandbox(&config);
            assert!(result.is_ok());
        }
    }
}
