//! FreeBSD-specific sandboxing using rlimit and basic controls.
//!
//! Provides sandboxing on FreeBSD using:
//! - BSD resource limits (rlimit)
//! - Filesystem access validation
//!
//! Note: Capsicum (capability mode) could be added later for stronger isolation.

use super::{limits, FilesystemMode, NetworkMode, SandboxConfig, SandboxError, SandboxResult};
use std::collections::HashSet;

/// Apply sandbox configuration to the current process (FreeBSD).
///
/// Uses BSD-style rlimit controls. Capsicum-only policies fail closed until a
/// child capability-mode entrypoint owns them.
pub fn apply_sandbox(config: &SandboxConfig) -> SandboxResult<()> {
    // Validate Capsicum-only policies before applying irreversible limits.
    apply_network_isolation(&config.network.mode)?;
    apply_filesystem_isolation(
        &config.filesystem.mode,
        &config.filesystem.read_paths,
        &config.filesystem.write_paths,
    )?;

    limits::apply_resource_limits(&config.limits)?;

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
        NetworkMode::None => Err(SandboxError::NetworkIsolation(
            "FreeBSD network isolation requires a Capsicum child".to_string(),
        )),
        NetworkMode::AllowList | NetworkMode::BlockList => Err(SandboxError::NetworkIsolation(
            "FreeBSD domain filtering requires a Capsicum child".to_string(),
        )),
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
            Err(SandboxError::FilesystemIsolation(
                "FreeBSD filesystem isolation requires a Capsicum child".to_string(),
            ))
        }
        FilesystemMode::Restricted => {
            tracing::debug!(
                "Filesystem: Restricted ({} read, {} write paths)",
                read_paths.len(),
                write_paths.len()
            );
            Err(SandboxError::FilesystemIsolation(
                "FreeBSD filesystem isolation requires a Capsicum child".to_string(),
            ))
        }
        FilesystemMode::Overlay => Err(SandboxError::FilesystemIsolation(
            "overlay filesystem isolation is unsupported on FreeBSD".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_basic_sandbox() {
        let config = SandboxConfig::new().with_cpu_time(Duration::from_secs(60));

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

        assert!(apply_sandbox(&configs[0]).is_ok());
        assert!(apply_sandbox(&configs[1]).is_err());
        assert!(apply_sandbox(&configs[2]).is_err());
    }
}
