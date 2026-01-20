//! Sandbox FFI bindings for Simple language.
//!
//! Provides FFI functions to configure and apply sandboxing from Simple code.
//! Uses a builder-style approach with a global config that can be modified
//! piece by piece before being applied.

use crate::sandbox::{apply_sandbox, cleanup_network_rules, FilesystemMode, NetworkMode, SandboxConfig};
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::Duration;

use lazy_static::lazy_static;

lazy_static! {
    /// Global sandbox configuration being built
    static ref SANDBOX_CONFIG: Mutex<SandboxConfig> = Mutex::new(SandboxConfig::new());
}

/// Reset the sandbox configuration to defaults.
#[no_mangle]
pub extern "C" fn rt_sandbox_reset() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        *config = SandboxConfig::new();
    }
}

/// Set CPU time limit in seconds.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_cpu_time(seconds: u64) {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.limits.cpu_time = Some(Duration::from_secs(seconds));
    }
}

/// Set memory limit in bytes.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_memory(bytes: u64) {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.limits.memory = Some(bytes);
    }
}

/// Set file descriptor limit.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_fd_limit(count: u64) {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.limits.file_descriptors = Some(count);
    }
}

/// Set thread limit.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_thread_limit(count: u64) {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.limits.threads = Some(count);
    }
}

/// Disable all network access.
#[no_mangle]
pub extern "C" fn rt_sandbox_disable_network() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.network.mode = NetworkMode::None;
    }
}

/// Set network mode to allowlist.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_network_allowlist() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.network.mode = NetworkMode::AllowList;
    }
}

/// Set network mode to blocklist.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_network_blocklist() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.network.mode = NetworkMode::BlockList;
    }
}

/// Add a domain to the network allowlist.
#[no_mangle]
pub unsafe extern "C" fn rt_sandbox_add_allowed_domain(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }

    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let domain = match std::str::from_utf8(slice) {
        Ok(s) => s.to_string(),
        Err(_) => return,
    };

    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.network.allowed_domains.insert(domain);
    }
}

/// Add a domain to the network blocklist.
#[no_mangle]
pub unsafe extern "C" fn rt_sandbox_add_blocked_domain(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }

    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let domain = match std::str::from_utf8(slice) {
        Ok(s) => s.to_string(),
        Err(_) => return,
    };

    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.network.blocked_domains.insert(domain);
    }
}

/// Set filesystem mode to read-only.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_fs_readonly() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.filesystem.mode = FilesystemMode::ReadOnly;
    }
}

/// Set filesystem mode to restricted.
#[no_mangle]
pub extern "C" fn rt_sandbox_set_fs_restricted() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.filesystem.mode = FilesystemMode::Restricted;
    }
}

/// Set filesystem mode to overlay (copy-on-write).
#[no_mangle]
pub extern "C" fn rt_sandbox_set_fs_overlay() {
    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.filesystem.mode = FilesystemMode::Overlay;
        config.filesystem.use_overlay = true;
    }
}

/// Add a path to the read-only paths list.
#[no_mangle]
pub unsafe extern "C" fn rt_sandbox_add_read_path(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }

    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let path = match std::str::from_utf8(slice) {
        Ok(s) => PathBuf::from(s),
        Err(_) => return,
    };

    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.filesystem.read_paths.insert(path);
    }
}

/// Add a path to the write paths list.
#[no_mangle]
pub unsafe extern "C" fn rt_sandbox_add_write_path(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }

    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let path = match std::str::from_utf8(slice) {
        Ok(s) => PathBuf::from(s),
        Err(_) => return,
    };

    if let Ok(mut config) = SANDBOX_CONFIG.lock() {
        config.filesystem.write_paths.insert(path);
    }
}

/// Apply the configured sandbox to the current process.
/// Returns true on success, false on failure.
#[no_mangle]
pub extern "C" fn rt_sandbox_apply() -> bool {
    let config = match SANDBOX_CONFIG.lock() {
        Ok(guard) => guard.clone(),
        Err(_) => return false,
    };

    match apply_sandbox(&config) {
        Ok(()) => true,
        Err(e) => {
            eprintln!("Sandbox error: {}", e);
            false
        }
    }
}

/// Cleanup network rules (Linux only, no-op on other platforms).
#[no_mangle]
pub extern "C" fn rt_sandbox_cleanup() {
    cleanup_network_rules();
}

/// Check if sandbox is currently configured (has any non-default settings).
#[no_mangle]
pub extern "C" fn rt_sandbox_is_configured() -> bool {
    if let Ok(config) = SANDBOX_CONFIG.lock() {
        // Check if any limits are set
        if config.limits.cpu_time.is_some()
            || config.limits.memory.is_some()
            || config.limits.file_descriptors.is_some()
            || config.limits.threads.is_some()
        {
            return true;
        }

        // Check if network mode is not Full
        if config.network.mode != NetworkMode::Full {
            return true;
        }

        // Check if filesystem mode is not Full
        if config.filesystem.mode != FilesystemMode::Full {
            return true;
        }

        false
    } else {
        false
    }
}

/// Get the current CPU time limit in seconds, or 0 if not set.
#[no_mangle]
pub extern "C" fn rt_sandbox_get_cpu_time() -> u64 {
    if let Ok(config) = SANDBOX_CONFIG.lock() {
        config.limits.cpu_time.map(|d| d.as_secs()).unwrap_or(0)
    } else {
        0
    }
}

/// Get the current memory limit in bytes, or 0 if not set.
#[no_mangle]
pub extern "C" fn rt_sandbox_get_memory() -> u64 {
    if let Ok(config) = SANDBOX_CONFIG.lock() {
        config.limits.memory.unwrap_or(0)
    } else {
        0
    }
}

/// Get the current network mode.
/// Returns: 0 = Full, 1 = None, 2 = AllowList, 3 = BlockList
#[no_mangle]
pub extern "C" fn rt_sandbox_get_network_mode() -> u8 {
    if let Ok(config) = SANDBOX_CONFIG.lock() {
        match config.network.mode {
            NetworkMode::Full => 0,
            NetworkMode::None => 1,
            NetworkMode::AllowList => 2,
            NetworkMode::BlockList => 3,
        }
    } else {
        0
    }
}

/// Get the current filesystem mode.
/// Returns: 0 = Full, 1 = ReadOnly, 2 = Restricted, 3 = Overlay
#[no_mangle]
pub extern "C" fn rt_sandbox_get_fs_mode() -> u8 {
    if let Ok(config) = SANDBOX_CONFIG.lock() {
        match config.filesystem.mode {
            FilesystemMode::Full => 0,
            FilesystemMode::ReadOnly => 1,
            FilesystemMode::Restricted => 2,
            FilesystemMode::Overlay => 3,
        }
    } else {
        0
    }
}
