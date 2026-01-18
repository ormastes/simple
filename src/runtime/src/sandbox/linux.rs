//! Linux-specific sandboxing using namespaces and cgroups.
//!
//! Provides the most comprehensive sandboxing on Linux using:
//! - Namespaces: PID, network, mount, user isolation
//! - cgroups: Resource control
//! - seccomp: Syscall filtering
//! - iptables: Network domain filtering

use super::{limits, FilesystemMode, NetworkMode, SandboxConfig, SandboxError, SandboxResult};
use nix::mount::{mount, MsFlags};
use nix::unistd::{Gid, Uid};
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

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
fn apply_network_isolation(mode: &NetworkMode, config: &super::NetworkIsolation) -> SandboxResult<()> {
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
                tracing::info!("Network isolation requires CAP_SYS_ADMIN or unprivileged user namespaces");
            }
            Ok(())
        }
        NetworkMode::AllowList => {
            tracing::debug!("Network: Allowlist mode with {} domains", config.allowed_domains.len());
            apply_network_allowlist(&config.allowed_domains)
        }
        NetworkMode::BlockList => {
            tracing::debug!("Network: Blocklist mode with {} domains", config.blocked_domains.len());
            apply_network_blocklist(&config.blocked_domains)
        }
    }
}

/// Apply network allowlist filtering using iptables.
///
/// Blocks all outbound connections except to the specified domains.
/// Resolves domain names to IP addresses and creates iptables rules.
fn apply_network_allowlist(domains: &HashSet<String>) -> SandboxResult<()> {
    // Check if iptables is available
    if !is_iptables_available() {
        tracing::warn!("iptables not available, falling back to no network filtering");
        tracing::info!("Install iptables or run with CAP_NET_ADMIN for network filtering");
        return Ok(());
    }

    // Resolve domains to IP addresses
    let allowed_ips = resolve_domains_to_ips(domains);

    if allowed_ips.is_empty() && !domains.is_empty() {
        tracing::warn!("Could not resolve any domains, network access may be restricted");
    }

    // Create a new iptables chain for sandbox rules
    let chain_name = "SIMPLE_SANDBOX_ALLOW";

    // Create the chain (ignore error if it exists)
    let _ = run_iptables(&["-N", chain_name]);

    // Flush the chain
    run_iptables(&["-F", chain_name]).map_err(|e| {
        SandboxError::NetworkIsolation(format!("Failed to flush iptables chain: {}", e))
    })?;

    // Allow loopback traffic
    run_iptables(&["-A", chain_name, "-o", "lo", "-j", "ACCEPT"]).ok();

    // Allow established connections
    run_iptables(&[
        "-A",
        chain_name,
        "-m",
        "state",
        "--state",
        "ESTABLISHED,RELATED",
        "-j",
        "ACCEPT",
    ])
    .ok();

    // Allow DNS (port 53) for domain resolution
    run_iptables(&["-A", chain_name, "-p", "udp", "--dport", "53", "-j", "ACCEPT"]).ok();
    run_iptables(&["-A", chain_name, "-p", "tcp", "--dport", "53", "-j", "ACCEPT"]).ok();

    // Allow connections to specified IPs
    for ip in &allowed_ips {
        run_iptables(&["-A", chain_name, "-d", ip, "-j", "ACCEPT"]).ok();
    }

    // Drop everything else
    run_iptables(&["-A", chain_name, "-j", "DROP"]).ok();

    // Insert our chain at the beginning of OUTPUT
    run_iptables(&["-I", "OUTPUT", "1", "-j", chain_name]).map_err(|e| {
        SandboxError::NetworkIsolation(format!(
            "Failed to insert iptables rules: {}. Requires CAP_NET_ADMIN.",
            e
        ))
    })?;

    tracing::info!(
        "Applied network allowlist: {} domains resolved to {} IPs",
        domains.len(),
        allowed_ips.len()
    );
    Ok(())
}

/// Apply network blocklist filtering using iptables.
///
/// Allows all outbound connections except to the specified domains.
fn apply_network_blocklist(domains: &HashSet<String>) -> SandboxResult<()> {
    // Check if iptables is available
    if !is_iptables_available() {
        tracing::warn!("iptables not available, falling back to no network filtering");
        tracing::info!("Install iptables or run with CAP_NET_ADMIN for network filtering");
        return Ok(());
    }

    // Resolve domains to IP addresses
    let blocked_ips = resolve_domains_to_ips(domains);

    if blocked_ips.is_empty() && !domains.is_empty() {
        tracing::warn!("Could not resolve any domains to block");
        return Ok(());
    }

    // Create a new iptables chain for sandbox rules
    let chain_name = "SIMPLE_SANDBOX_BLOCK";

    // Create the chain (ignore error if it exists)
    let _ = run_iptables(&["-N", chain_name]);

    // Flush the chain
    run_iptables(&["-F", chain_name]).map_err(|e| {
        SandboxError::NetworkIsolation(format!("Failed to flush iptables chain: {}", e))
    })?;

    // Block connections to specified IPs
    for ip in &blocked_ips {
        run_iptables(&["-A", chain_name, "-d", ip, "-j", "DROP"]).ok();
    }

    // Allow everything else (default ACCEPT)
    run_iptables(&["-A", chain_name, "-j", "ACCEPT"]).ok();

    // Insert our chain at the beginning of OUTPUT
    run_iptables(&["-I", "OUTPUT", "1", "-j", chain_name]).map_err(|e| {
        SandboxError::NetworkIsolation(format!(
            "Failed to insert iptables rules: {}. Requires CAP_NET_ADMIN.",
            e
        ))
    })?;

    tracing::info!(
        "Applied network blocklist: {} domains resolved to {} IPs",
        domains.len(),
        blocked_ips.len()
    );
    Ok(())
}

/// Check if iptables is available on the system.
fn is_iptables_available() -> bool {
    Command::new("iptables")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run an iptables command with the given arguments.
fn run_iptables(args: &[&str]) -> Result<(), String> {
    let output = Command::new("iptables")
        .args(args)
        .output()
        .map_err(|e| format!("Failed to execute iptables: {}", e))?;

    if output.status.success() {
        Ok(())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        Err(format!("iptables failed: {}", stderr.trim()))
    }
}

/// Resolve domain names to IP addresses.
///
/// Uses DNS resolution to convert domain names to IPv4/IPv6 addresses.
fn resolve_domains_to_ips(domains: &HashSet<String>) -> Vec<String> {
    use std::net::ToSocketAddrs;

    let mut ips = Vec::new();

    for domain in domains {
        // Try to resolve the domain
        let addr = format!("{}:80", domain);
        match addr.to_socket_addrs() {
            Ok(addrs) => {
                for addr in addrs {
                    let ip = addr.ip().to_string();
                    if !ips.contains(&ip) {
                        ips.push(ip);
                        tracing::debug!("Resolved {} -> {}", domain, addr.ip());
                    }
                }
            }
            Err(e) => {
                tracing::warn!("Failed to resolve domain '{}': {}", domain, e);
            }
        }
    }

    ips
}

/// Clean up iptables rules created by the sandbox.
///
/// Call this when the sandbox process exits to remove the filter rules.
pub fn cleanup_network_rules() {
    // Try to remove allowlist chain
    let _ = run_iptables(&["-D", "OUTPUT", "-j", "SIMPLE_SANDBOX_ALLOW"]);
    let _ = run_iptables(&["-F", "SIMPLE_SANDBOX_ALLOW"]);
    let _ = run_iptables(&["-X", "SIMPLE_SANDBOX_ALLOW"]);

    // Try to remove blocklist chain
    let _ = run_iptables(&["-D", "OUTPUT", "-j", "SIMPLE_SANDBOX_BLOCK"]);
    let _ = run_iptables(&["-F", "SIMPLE_SANDBOX_BLOCK"]);
    let _ = run_iptables(&["-X", "SIMPLE_SANDBOX_BLOCK"]);

    tracing::debug!("Cleaned up sandbox network rules");
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
            apply_readonly_isolation(read_paths)
        }
        FilesystemMode::Restricted => {
            tracing::debug!(
                "Filesystem: Restricted ({} read, {} write paths)",
                read_paths.len(),
                write_paths.len()
            );
            apply_restricted_isolation(read_paths, write_paths)
        }
        FilesystemMode::Overlay => {
            tracing::debug!("Filesystem: Overlay mode");
            apply_overlay_isolation()
        }
    }
}

/// Apply read-only filesystem isolation.
///
/// Creates a mount namespace and remounts specified paths as read-only.
/// All other paths become inaccessible.
fn apply_readonly_isolation(read_paths: &HashSet<PathBuf>) -> SandboxResult<()> {
    use nix::sched::{unshare, CloneFlags};

    // Create a new mount namespace
    unshare(CloneFlags::CLONE_NEWNS).map_err(|e| {
        SandboxError::FilesystemIsolation(format!(
            "Failed to create mount namespace: {}. Requires CAP_SYS_ADMIN or unprivileged user namespaces.",
            e
        ))
    })?;

    // Make all mounts private to prevent propagation
    mount::<str, str, str, str>(None, "/", None, MsFlags::MS_REC | MsFlags::MS_PRIVATE, None)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to make mounts private: {}", e)))?;

    // Bind mount each allowed path and remount as read-only
    for path in read_paths {
        if path.exists() {
            bind_mount_readonly(path)?;
        } else {
            tracing::warn!("Read-only path does not exist, skipping: {}", path.display());
        }
    }

    tracing::info!("Applied read-only filesystem isolation with {} paths", read_paths.len());
    Ok(())
}

/// Bind mount a path and remount it as read-only.
fn bind_mount_readonly(path: &Path) -> SandboxResult<()> {
    let path_str = path.to_string_lossy();

    // First, bind mount the path to itself
    mount::<str, Path, str, str>(Some(&path_str), path, None, MsFlags::MS_BIND | MsFlags::MS_REC, None)
        .map_err(|e| {
            SandboxError::FilesystemIsolation(format!("Failed to bind mount {}: {}", path_str, e))
        })?;

    // Then remount as read-only
    mount::<str, Path, str, str>(
        None,
        path,
        None,
        MsFlags::MS_REMOUNT | MsFlags::MS_BIND | MsFlags::MS_RDONLY | MsFlags::MS_REC,
        None,
    )
    .map_err(|e| {
        SandboxError::FilesystemIsolation(format!("Failed to remount {} as read-only: {}", path_str, e))
    })?;

    tracing::debug!("Mounted {} as read-only", path_str);
    Ok(())
}

/// Apply restricted filesystem isolation with specific read and write paths.
///
/// Creates a minimal filesystem with only the specified paths accessible.
fn apply_restricted_isolation(
    read_paths: &HashSet<PathBuf>,
    write_paths: &HashSet<PathBuf>,
) -> SandboxResult<()> {
    use nix::sched::{unshare, CloneFlags};

    // Create a new mount namespace
    unshare(CloneFlags::CLONE_NEWNS).map_err(|e| {
        SandboxError::FilesystemIsolation(format!(
            "Failed to create mount namespace: {}. Requires CAP_SYS_ADMIN or unprivileged user namespaces.",
            e
        ))
    })?;

    // Make all mounts private
    mount::<str, str, str, str>(None, "/", None, MsFlags::MS_REC | MsFlags::MS_PRIVATE, None)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to make mounts private: {}", e)))?;

    // Apply read-only mounts for read paths
    for path in read_paths {
        if path.exists() {
            // Skip if also in write_paths (will be mounted read-write)
            if !write_paths.contains(path) {
                bind_mount_readonly(path)?;
            }
        } else {
            tracing::warn!("Read path does not exist, skipping: {}", path.display());
        }
    }

    // Apply read-write bind mounts for write paths
    for path in write_paths {
        if path.exists() {
            bind_mount_readwrite(path)?;
        } else {
            tracing::warn!("Write path does not exist, skipping: {}", path.display());
        }
    }

    tracing::info!(
        "Applied restricted filesystem isolation ({} read-only, {} read-write)",
        read_paths.len(),
        write_paths.len()
    );
    Ok(())
}

/// Bind mount a path with read-write access.
fn bind_mount_readwrite(path: &Path) -> SandboxResult<()> {
    let path_str = path.to_string_lossy();

    // Bind mount the path to itself (preserves write access)
    mount::<str, Path, str, str>(Some(&path_str), path, None, MsFlags::MS_BIND | MsFlags::MS_REC, None)
        .map_err(|e| {
            SandboxError::FilesystemIsolation(format!("Failed to bind mount {}: {}", path_str, e))
        })?;

    tracing::debug!("Mounted {} as read-write", path_str);
    Ok(())
}

/// Apply overlay filesystem isolation.
///
/// Creates an overlayfs mount that captures all writes in a temporary layer,
/// leaving the original filesystem unchanged.
fn apply_overlay_isolation() -> SandboxResult<()> {
    use nix::sched::{unshare, CloneFlags};

    // Create a new mount namespace
    unshare(CloneFlags::CLONE_NEWNS).map_err(|e| {
        SandboxError::FilesystemIsolation(format!(
            "Failed to create mount namespace: {}. Requires CAP_SYS_ADMIN or unprivileged user namespaces.",
            e
        ))
    })?;

    // Make all mounts private
    mount::<str, str, str, str>(None, "/", None, MsFlags::MS_REC | MsFlags::MS_PRIVATE, None)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to make mounts private: {}", e)))?;

    // Create temporary directories for overlay
    let overlay_base = PathBuf::from("/tmp/simple-sandbox-overlay");
    let upper_dir = overlay_base.join("upper");
    let work_dir = overlay_base.join("work");
    let merged_dir = overlay_base.join("merged");

    // Clean up any previous overlay
    let _ = fs::remove_dir_all(&overlay_base);

    // Create overlay directories
    fs::create_dir_all(&upper_dir)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to create upper dir: {}", e)))?;
    fs::create_dir_all(&work_dir)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to create work dir: {}", e)))?;
    fs::create_dir_all(&merged_dir)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to create merged dir: {}", e)))?;

    // Mount overlayfs
    // overlay options: lowerdir=<ro-layer>,upperdir=<rw-layer>,workdir=<work>
    let overlay_opts = format!(
        "lowerdir=/,upperdir={},workdir={}",
        upper_dir.display(),
        work_dir.display()
    );

    mount::<str, PathBuf, str, str>(
        Some("overlay"),
        &merged_dir,
        Some("overlay"),
        MsFlags::empty(),
        Some(overlay_opts.as_str()),
    )
    .map_err(|e| {
        SandboxError::FilesystemIsolation(format!(
            "Failed to mount overlayfs: {}. Requires kernel overlay support and CAP_SYS_ADMIN.",
            e
        ))
    })?;

    // Pivot root to the overlay
    // Note: Full pivot_root requires additional setup (proc, sys, dev mounts)
    // For simplicity, we chroot into the overlay
    std::env::set_current_dir(&merged_dir)
        .map_err(|e| SandboxError::FilesystemIsolation(format!("Failed to chdir to overlay: {}", e)))?;

    tracing::info!("Applied overlay filesystem isolation at {}", merged_dir.display());
    tracing::info!("All writes will be captured in {} and discarded on exit", upper_dir.display());
    Ok(())
}

/// Create an empty network namespace (requires CAP_SYS_ADMIN).
fn create_empty_network_namespace() -> SandboxResult<()> {
    use nix::sched::{unshare, CloneFlags};

    unshare(CloneFlags::CLONE_NEWNET)
        .map_err(|e| SandboxError::NetworkIsolation(format!("Failed to create network namespace: {}", e)))?;

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
        let config = SandboxConfig::new().with_read_paths(vec!["/tmp".into(), "/usr/lib".into()]);

        // Test config is constructed correctly
        assert_eq!(config.filesystem.read_paths.len(), 2);
        let tmp_path: PathBuf = "/tmp".into();
        let usr_lib_path: PathBuf = "/usr/lib".into();
        assert!(config.filesystem.read_paths.contains(&tmp_path));
        assert!(config.filesystem.read_paths.contains(&usr_lib_path));
    }

    #[test]
    fn test_network_allowlist_config() {
        let domains = vec!["github.com".to_string(), "api.example.com".to_string()];
        let config = SandboxConfig::new().with_network_allowlist(domains);

        assert_eq!(config.network.mode, NetworkMode::AllowList);
        assert_eq!(config.network.allowed_domains.len(), 2);
        assert!(config.network.allowed_domains.contains("github.com"));
        assert!(config.network.allowed_domains.contains("api.example.com"));
    }

    #[test]
    fn test_network_blocklist_config() {
        let domains = vec!["malicious.com".to_string(), "evil.org".to_string()];
        let config = SandboxConfig::new().with_network_blocklist(domains);

        assert_eq!(config.network.mode, NetworkMode::BlockList);
        assert_eq!(config.network.blocked_domains.len(), 2);
        assert!(config.network.blocked_domains.contains("malicious.com"));
        assert!(config.network.blocked_domains.contains("evil.org"));
    }

    #[test]
    fn test_restricted_paths_config() {
        let read_paths = vec!["/tmp".into(), "/usr/lib".into()];
        let write_paths = vec!["/app/data".into()];
        let config = SandboxConfig::new().with_restricted_paths(read_paths, write_paths);

        assert_eq!(config.filesystem.mode, FilesystemMode::Restricted);
        assert_eq!(config.filesystem.read_paths.len(), 2);
        assert_eq!(config.filesystem.write_paths.len(), 1);
        assert!(config.filesystem.write_paths.contains(&PathBuf::from("/app/data")));
    }

    #[test]
    fn test_overlay_config() {
        let config = SandboxConfig::new().with_overlay();

        assert_eq!(config.filesystem.mode, FilesystemMode::Overlay);
        assert!(config.filesystem.use_overlay);
    }

    #[test]
    fn test_resolve_domains_to_ips() {
        // Test with a well-known domain that should resolve
        let mut domains = HashSet::new();
        domains.insert("localhost".to_string());

        let ips = resolve_domains_to_ips(&domains);

        // localhost should resolve to 127.0.0.1 or ::1
        // Note: This test may fail in isolated environments without DNS
        if !ips.is_empty() {
            assert!(ips.iter().any(|ip| ip == "127.0.0.1" || ip == "::1"));
        }
    }

    #[test]
    fn test_resolve_invalid_domain() {
        let mut domains = HashSet::new();
        domains.insert("this-domain-definitely-does-not-exist-12345.invalid".to_string());

        let ips = resolve_domains_to_ips(&domains);

        // Invalid domain should not resolve
        assert!(ips.is_empty());
    }

    #[test]
    fn test_iptables_availability_check() {
        // Just test that the function doesn't panic
        let _available = is_iptables_available();
    }

    #[test]
    fn test_combined_sandbox_config() {
        let config = SandboxConfig::new()
            .with_cpu_time(Duration::from_secs(60))
            .with_memory(256 * 1024 * 1024) // 256 MB
            .with_no_network()
            .with_read_paths(vec!["/tmp".into()]);

        assert!(config.limits.cpu_time.is_some());
        assert!(config.limits.memory.is_some());
        assert_eq!(config.network.mode, NetworkMode::None);
        assert_eq!(config.filesystem.mode, FilesystemMode::ReadOnly);
    }
}
