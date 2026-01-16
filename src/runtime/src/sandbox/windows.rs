//! Windows-specific sandboxing using Job Objects and AppContainers.
//!
//! Provides sandboxing on Windows using:
//! - Job Objects: Resource control and process containment
//! - AppContainers: Security isolation (requires Windows 8+)

use super::{limits, FilesystemMode, NetworkMode, SandboxConfig, SandboxError, SandboxResult};
use std::collections::HashSet;
use std::ptr;
use windows::Win32::Foundation::{CloseHandle, HANDLE};
use windows::Win32::System::JobObjects::*;
use windows::Win32::System::Threading::{GetCurrentProcess, OpenProcess, PROCESS_ALL_ACCESS};

/// Apply sandbox configuration to the current process (Windows).
///
/// This uses Windows Job Objects for resource control and process containment.
/// AppContainer isolation requires Windows 8+ and is not applied to already-running processes.
pub fn apply_sandbox(config: &SandboxConfig) -> SandboxResult<()> {
    // Apply basic resource limits
    limits::apply_resource_limits(&config.limits)?;

    // Create and configure a Job Object
    let job = create_job_object()?;

    // Configure the Job Object based on config
    configure_job_limits(&job, config)?;

    // Assign current process to the Job Object
    assign_to_job(&job)?;

    // Apply network isolation (limited without AppContainer)
    apply_network_isolation(&config.network.mode)?;

    // Apply filesystem isolation (limited without AppContainer)
    apply_filesystem_isolation(
        &config.filesystem.mode,
        &config.filesystem.read_paths,
        &config.filesystem.write_paths,
    )?;

    tracing::info!("Applied Windows sandboxing using Job Objects");

    Ok(())
}

/// Create a new Job Object.
fn create_job_object() -> SandboxResult<HANDLE> {
    unsafe {
        let job = CreateJobObjectW(None, None)
            .map_err(|e| SandboxError::Config(format!("Failed to create Job Object: {}", e)))?;

        if job.is_invalid() {
            return Err(SandboxError::Config(
                "CreateJobObjectW returned invalid handle".to_string(),
            ));
        }

        Ok(job)
    }
}

/// Configure Job Object limits.
fn configure_job_limits(job: &HANDLE, config: &SandboxConfig) -> SandboxResult<()> {
    unsafe {
        let mut info: JOBOBJECT_EXTENDED_LIMIT_INFORMATION = std::mem::zeroed();

        // Set CPU time limit
        if let Some(cpu_time) = config.limits.cpu_time {
            let time_100ns = cpu_time.as_secs() * 10_000_000; // Convert to 100ns units
            info.BasicLimitInformation.PerProcessUserTimeLimit = time_100ns as i64;
            info.BasicLimitInformation.LimitFlags |= JOB_OBJECT_LIMIT_PROCESS_TIME;
        }

        // Set memory limit
        if let Some(memory) = config.limits.memory {
            info.ProcessMemoryLimit = memory as usize;
            info.BasicLimitInformation.LimitFlags |= JOB_OBJECT_LIMIT_PROCESS_MEMORY;
        }

        // Set process limit (equivalent to thread limit)
        if let Some(threads) = config.limits.threads {
            info.BasicLimitInformation.ActiveProcessLimit = threads as u32;
            info.BasicLimitInformation.LimitFlags |= JOB_OBJECT_LIMIT_ACTIVE_PROCESS;
        }

        // Kill all processes when the job is closed
        info.BasicLimitInformation.LimitFlags |= JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;

        // Apply the limits
        SetInformationJobObject(
            *job,
            JobObjectExtendedLimitInformation,
            &info as *const _ as *const _,
            std::mem::size_of::<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>() as u32,
        )
        .map_err(|e| SandboxError::ResourceLimit(format!("Failed to set Job Object limits: {}", e)))?;

        tracing::debug!("Configured Job Object limits");
    }

    Ok(())
}

/// Assign the current process to the Job Object.
fn assign_to_job(job: &HANDLE) -> SandboxResult<()> {
    unsafe {
        let process = GetCurrentProcess();

        AssignProcessToJobObject(*job, process)
            .map_err(|e| SandboxError::Config(format!("Failed to assign process to Job Object: {}", e)))?;

        tracing::debug!("Assigned current process to Job Object");
    }

    Ok(())
}

/// Apply network isolation on Windows.
///
/// Full network isolation requires AppContainer, which cannot be applied to
/// already-running processes. We log warnings and suggest alternatives.
fn apply_network_isolation(mode: &NetworkMode) -> SandboxResult<()> {
    match mode {
        NetworkMode::Full => {
            tracing::debug!("Network: Full access");
            Ok(())
        }
        NetworkMode::None => {
            tracing::warn!("Network isolation on Windows requires AppContainer or Windows Firewall rules");
            tracing::info!("Consider using: simple run --sandbox=docker script.spl or configure Windows Firewall");
            Ok(())
        }
        NetworkMode::AllowList | NetworkMode::BlockList => {
            tracing::warn!("Domain filtering on Windows requires AppContainer or Windows Firewall rules");
            Ok(())
        }
    }
}

/// Apply filesystem isolation on Windows.
///
/// Full filesystem isolation requires AppContainer or running as a different user.
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
            tracing::warn!("Filesystem isolation on Windows requires AppContainer or NTFS permissions");
            Ok(())
        }
        FilesystemMode::Restricted => {
            tracing::debug!(
                "Filesystem: Restricted ({} read, {} write paths)",
                read_paths.len(),
                write_paths.len()
            );
            tracing::warn!("Filesystem isolation on Windows requires AppContainer or NTFS permissions");
            Ok(())
        }
        FilesystemMode::Overlay => {
            tracing::warn!("Overlay filesystem not supported on Windows - use Docker");
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
            .with_cpu_time(Duration::from_secs(60))
            .with_memory(1024 * 1024 * 1024); // 1 GB (safe for tests)

        // This should succeed on Windows
        let result = apply_sandbox(&config);
        assert!(result.is_ok());
    }

    #[test]
    fn test_job_object_creation() {
        let result = create_job_object();
        assert!(result.is_ok());

        // Clean up
        if let Ok(job) = result {
            unsafe {
                let _ = CloseHandle(job);
            }
        }
    }

    #[test]
    fn test_memory_limit() {
        let config = SandboxConfig::new().with_memory(512 * 1024 * 1024); // 512 MB (safe for tests)

        let result = apply_sandbox(&config);
        assert!(result.is_ok());
    }
}
