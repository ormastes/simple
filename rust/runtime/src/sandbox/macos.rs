//! macOS-specific sandboxing using sandbox-exec and BSD controls.
//!
//! Provides sandboxing on macOS using:
//! - sandbox-exec: Apple's sandboxing framework
//! - BSD resource limits
//! - File system controls

use super::{limits, FilesystemMode, NetworkMode, SandboxConfig, SandboxError, SandboxResult};
use std::collections::HashSet;

/// Apply sandbox configuration to the current process (macOS).
///
/// This uses macOS sandbox-exec and BSD-style controls.
/// Note: Full sandbox-exec requires the process to be re-executed with
/// the sandbox profile, which is not possible for an already running process.
/// We apply what we can: resource limits and filesystem checks.
pub fn apply_sandbox(config: &SandboxConfig) -> SandboxResult<()> {
    // Apply basic resource limits (BSD-style rlimit)
    limits::apply_resource_limits(&config.limits)?;

    // Apply network isolation (limited on macOS without re-exec)
    apply_network_isolation(&config.network.mode)?;

    // Apply filesystem isolation (limited on macOS without re-exec)
    apply_filesystem_isolation(
        &config.filesystem.mode,
        &config.filesystem.read_paths,
        &config.filesystem.write_paths,
    )?;

    tracing::info!("Applied macOS sandboxing (limited - consider using Docker for full isolation)");

    Ok(())
}

/// Apply network isolation on macOS.
///
/// macOS sandboxing requires using sandbox-exec, which needs process re-execution.
/// For runtime sandboxing, we can only log warnings and suggest alternatives.
fn apply_network_isolation(mode: &NetworkMode) -> SandboxResult<()> {
    match mode {
        NetworkMode::Full => {
            tracing::debug!("Network: Full access");
            Ok(())
        }
        NetworkMode::None => {
            tracing::warn!("Network isolation on macOS requires sandbox-exec re-execution or Docker");
            tracing::info!("Consider using: simple run --sandbox=docker script.spl");
            Ok(())
        }
        NetworkMode::AllowList | NetworkMode::BlockList => {
            tracing::warn!("Domain filtering on macOS requires sandbox-exec re-execution or Docker");
            Ok(())
        }
    }
}

/// Apply filesystem isolation on macOS.
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
            tracing::warn!("Filesystem isolation on macOS requires sandbox-exec re-execution or Docker");
            Ok(())
        }
        FilesystemMode::Restricted => {
            tracing::debug!(
                "Filesystem: Restricted ({} read, {} write paths)",
                read_paths.len(),
                write_paths.len()
            );
            tracing::warn!("Filesystem isolation on macOS requires sandbox-exec re-execution or Docker");
            Ok(())
        }
        FilesystemMode::Overlay => {
            tracing::warn!("Overlay filesystem not supported on macOS - use Docker");
            Ok(())
        }
    }
}

/// Generate a sandbox profile for macOS sandbox-exec.
///
/// This can be used to re-execute the process with proper sandboxing.
/// Example usage:
/// ```bash
/// sandbox-exec -p "$(cat profile.sb)" simple run script.spl
/// ```
pub fn generate_sandbox_profile(config: &SandboxConfig) -> String {
    let mut profile = String::from("(version 1)\n");

    // Default deny all
    profile.push_str("(deny default)\n");

    // Allow basic operations needed for execution
    profile.push_str("(allow process*)\n");
    profile.push_str("(allow sysctl-read)\n");

    // Network rules
    match config.network.mode {
        NetworkMode::Full => {
            profile.push_str("(allow network*)\n");
        }
        NetworkMode::None => {
            // Network already denied by default
        }
        NetworkMode::AllowList => {
            // Would need specific domain rules
            profile.push_str("; Network allowlist - implement domain-specific rules\n");
        }
        NetworkMode::BlockList => {
            profile.push_str("(allow network*)\n");
            profile.push_str("; Network blocklist - implement domain-specific deny rules\n");
        }
    }

    // Filesystem rules
    match config.filesystem.mode {
        FilesystemMode::Full => {
            profile.push_str("(allow file-read* file-write*)\n");
        }
        FilesystemMode::ReadOnly => {
            for path in &config.filesystem.read_paths {
                profile.push_str(&format!("(allow file-read* (subpath \"{}\"))\n", path.display()));
            }
        }
        FilesystemMode::Restricted => {
            for path in &config.filesystem.read_paths {
                profile.push_str(&format!("(allow file-read* (subpath \"{}\"))\n", path.display()));
            }
            for path in &config.filesystem.write_paths {
                profile.push_str(&format!("(allow file-write* (subpath \"{}\"))\n", path.display()));
            }
        }
        FilesystemMode::Overlay => {
            profile.push_str("; Overlay mode not supported\n");
        }
    }

    profile
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    #[ignore] // sandbox_init may fail on CI macOS (deprecated API)
    fn test_basic_sandbox() {
        let config = SandboxConfig::new()
            .with_cpu_time(Duration::from_secs(60))
            .with_memory(1024 * 1024 * 1024); // 1 GB (safe for tests)

        // This should succeed (basic limits work on macOS)
        let result = apply_sandbox(&config);
        assert!(result.is_ok());
    }

    #[test]
    fn test_sandbox_profile_generation() {
        let config = SandboxConfig::new()
            .with_no_network()
            .with_read_paths(vec!["/tmp".into(), "/usr/lib".into()]);

        let profile = generate_sandbox_profile(&config);

        // Check that profile contains expected rules
        assert!(profile.contains("(version 1)"));
        assert!(profile.contains("(deny default)"));
        assert!(profile.contains("/tmp"));
        assert!(profile.contains("/usr/lib"));
    }

    #[test]
    fn test_network_modes() {
        let configs = vec![
            SandboxConfig::new(), // Full network
            SandboxConfig::new().with_no_network(),
            SandboxConfig::new().with_network_allowlist(vec!["example.com".to_string()]),
        ];

        for config in configs {
            let result = apply_sandbox(&config);
            assert!(result.is_ok());
        }
    }
}
