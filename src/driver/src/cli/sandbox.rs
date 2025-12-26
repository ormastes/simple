//! Sandboxing configuration for the Simple CLI.

use simple_runtime::SandboxConfig;
use std::path::PathBuf;
use std::time::Duration;

/// Parse memory size from string (supports K, M, G suffixes)
pub fn parse_memory_size(s: &str) -> Result<u64, String> {
    let s = s.trim();
    let (num_str, multiplier) = if s.ends_with('G') || s.ends_with('g') {
        (&s[..s.len() - 1], 1024 * 1024 * 1024)
    } else if s.ends_with('M') || s.ends_with('m') {
        (&s[..s.len() - 1], 1024 * 1024)
    } else if s.ends_with('K') || s.ends_with('k') {
        (&s[..s.len() - 1], 1024)
    } else {
        (s, 1)
    };

    num_str
        .parse::<u64>()
        .map(|n| n * multiplier)
        .map_err(|e| format!("invalid memory size '{}': {}", s, e))
}

/// Parse sandbox configuration from command-line arguments
pub fn parse_sandbox_config(args: &[String]) -> Option<SandboxConfig> {
    // Check if sandboxing is enabled at all
    let has_sandbox_flag = args.iter().any(|a| {
        a == "--sandbox"
            || a.starts_with("--time-limit")
            || a.starts_with("--memory-limit")
            || a.starts_with("--fd-limit")
            || a.starts_with("--thread-limit")
            || a == "--no-network"
            || a.starts_with("--network-allow")
            || a.starts_with("--network-block")
            || a.starts_with("--read-only")
            || a.starts_with("--read-write")
    });

    if !has_sandbox_flag {
        return None;
    }

    let mut config = SandboxConfig::new();

    // Parse resource limits
    for i in 0..args.len() {
        let arg = &args[i];

        if arg == "--time-limit" && i + 1 < args.len() {
            if let Ok(secs) = args[i + 1].parse::<u64>() {
                config = config.with_cpu_time(Duration::from_secs(secs));
            }
        } else if arg == "--memory-limit" && i + 1 < args.len() {
            if let Ok(bytes) = parse_memory_size(&args[i + 1]) {
                config = config.with_memory(bytes);
            }
        } else if arg == "--fd-limit" && i + 1 < args.len() {
            if let Ok(count) = args[i + 1].parse::<u64>() {
                config = config.with_file_descriptors(count);
            }
        } else if arg == "--thread-limit" && i + 1 < args.len() {
            if let Ok(count) = args[i + 1].parse::<u64>() {
                config = config.with_threads(count);
            }
        } else if arg == "--no-network" {
            config = config.with_no_network();
        } else if arg == "--network-allow" && i + 1 < args.len() {
            let domains: Vec<String> = args[i + 1].split(',').map(|s| s.trim().to_string()).collect();
            config = config.with_network_allowlist(domains);
        } else if arg == "--network-block" && i + 1 < args.len() {
            let domains: Vec<String> = args[i + 1].split(',').map(|s| s.trim().to_string()).collect();
            config = config.with_network_blocklist(domains);
        } else if arg == "--read-only" && i + 1 < args.len() {
            let paths: Vec<PathBuf> = args[i + 1]
                .split(',')
                .map(|s| PathBuf::from(s.trim()))
                .collect();
            config = config.with_read_paths(paths);
        } else if arg == "--read-write" && i + 1 < args.len() {
            let read_write: Vec<&str> = args[i + 1].split(',').collect();
            let paths: Vec<PathBuf> = read_write
                .iter()
                .map(|s| PathBuf::from(s.trim()))
                .collect();
            // For --read-write, set both read and write paths to the same set
            config = config.with_restricted_paths(paths.clone(), paths);
        }
    }

    Some(config)
}

/// Apply sandbox configuration to the current process
pub fn apply_sandbox(config: &SandboxConfig) -> Result<(), String> {
    simple_runtime::apply_sandbox(config)
        .map_err(|e| format!("Failed to apply sandbox: {}", e))
}
