//! Sandbox operations extern functions
//!
//! Functions for configuring and applying process sandboxing.
//! Uses a builder pattern where configuration is built up piece by piece
//! before being applied.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::value::ffi::{
    rt_sandbox_reset, rt_sandbox_set_cpu_time, rt_sandbox_set_memory, rt_sandbox_set_fd_limit,
    rt_sandbox_set_thread_limit, rt_sandbox_disable_network, rt_sandbox_set_network_allowlist,
    rt_sandbox_set_network_blocklist, rt_sandbox_add_allowed_domain, rt_sandbox_add_blocked_domain,
    rt_sandbox_set_fs_readonly, rt_sandbox_set_fs_restricted, rt_sandbox_set_fs_overlay, rt_sandbox_add_read_path,
    rt_sandbox_add_write_path, rt_sandbox_apply, rt_sandbox_cleanup, rt_sandbox_is_configured, rt_sandbox_get_cpu_time,
    rt_sandbox_get_memory, rt_sandbox_get_network_mode, rt_sandbox_get_fs_mode,
};

/// Reset the sandbox configuration to defaults.
///
/// Callable from Simple as: `rt_sandbox_reset()`
pub fn rt_sandbox_reset_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_reset();
    Ok(Value::Nil)
}

/// Set CPU time limit in seconds.
///
/// Callable from Simple as: `rt_sandbox_set_cpu_time(seconds)`
pub fn rt_sandbox_set_cpu_time_fn(args: &[Value]) -> Result<Value, CompileError> {
    let seconds = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        Some(Value::Float(f)) => *f as u64,
        _ => {
            return Err(CompileError::runtime(
                "rt_sandbox_set_cpu_time: seconds must be a number",
            ))
        }
    };
    rt_sandbox_set_cpu_time(seconds);
    Ok(Value::Nil)
}

/// Set memory limit in bytes.
///
/// Callable from Simple as: `rt_sandbox_set_memory(bytes)`
pub fn rt_sandbox_set_memory_fn(args: &[Value]) -> Result<Value, CompileError> {
    let bytes = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        Some(Value::Float(f)) => *f as u64,
        _ => return Err(CompileError::runtime("rt_sandbox_set_memory: bytes must be a number")),
    };
    rt_sandbox_set_memory(bytes);
    Ok(Value::Nil)
}

/// Set file descriptor limit.
///
/// Callable from Simple as: `rt_sandbox_set_fd_limit(count)`
pub fn rt_sandbox_set_fd_limit_fn(args: &[Value]) -> Result<Value, CompileError> {
    let count = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        Some(Value::Float(f)) => *f as u64,
        _ => return Err(CompileError::runtime("rt_sandbox_set_fd_limit: count must be a number")),
    };
    rt_sandbox_set_fd_limit(count);
    Ok(Value::Nil)
}

/// Set thread limit.
///
/// Callable from Simple as: `rt_sandbox_set_thread_limit(count)`
pub fn rt_sandbox_set_thread_limit_fn(args: &[Value]) -> Result<Value, CompileError> {
    let count = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        Some(Value::Float(f)) => *f as u64,
        _ => {
            return Err(CompileError::runtime(
                "rt_sandbox_set_thread_limit: count must be a number",
            ))
        }
    };
    rt_sandbox_set_thread_limit(count);
    Ok(Value::Nil)
}

/// Disable all network access.
///
/// Callable from Simple as: `rt_sandbox_disable_network()`
pub fn rt_sandbox_disable_network_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_disable_network();
    Ok(Value::Nil)
}

/// Set network mode to allowlist.
///
/// Callable from Simple as: `rt_sandbox_set_network_allowlist()`
pub fn rt_sandbox_set_network_allowlist_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_set_network_allowlist();
    Ok(Value::Nil)
}

/// Set network mode to blocklist.
///
/// Callable from Simple as: `rt_sandbox_set_network_blocklist()`
pub fn rt_sandbox_set_network_blocklist_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_set_network_blocklist();
    Ok(Value::Nil)
}

/// Add a domain to the network allowlist.
///
/// Callable from Simple as: `rt_sandbox_add_allowed_domain(domain)`
pub fn rt_sandbox_add_allowed_domain_fn(args: &[Value]) -> Result<Value, CompileError> {
    let domain = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_sandbox_add_allowed_domain: domain must be a string",
            ))
        }
    };
    unsafe {
        rt_sandbox_add_allowed_domain(domain.as_ptr(), domain.len() as u64);
    }
    Ok(Value::Nil)
}

/// Add a domain to the network blocklist.
///
/// Callable from Simple as: `rt_sandbox_add_blocked_domain(domain)`
pub fn rt_sandbox_add_blocked_domain_fn(args: &[Value]) -> Result<Value, CompileError> {
    let domain = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_sandbox_add_blocked_domain: domain must be a string",
            ))
        }
    };
    unsafe {
        rt_sandbox_add_blocked_domain(domain.as_ptr(), domain.len() as u64);
    }
    Ok(Value::Nil)
}

/// Set filesystem mode to read-only.
///
/// Callable from Simple as: `rt_sandbox_set_fs_readonly()`
pub fn rt_sandbox_set_fs_readonly_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_set_fs_readonly();
    Ok(Value::Nil)
}

/// Set filesystem mode to restricted.
///
/// Callable from Simple as: `rt_sandbox_set_fs_restricted()`
pub fn rt_sandbox_set_fs_restricted_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_set_fs_restricted();
    Ok(Value::Nil)
}

/// Set filesystem mode to overlay (copy-on-write).
///
/// Callable from Simple as: `rt_sandbox_set_fs_overlay()`
pub fn rt_sandbox_set_fs_overlay_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_set_fs_overlay();
    Ok(Value::Nil)
}

/// Add a path to the read-only paths list.
///
/// Callable from Simple as: `rt_sandbox_add_read_path(path)`
pub fn rt_sandbox_add_read_path_fn(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Err(CompileError::runtime("rt_sandbox_add_read_path: path must be a string")),
    };
    unsafe {
        rt_sandbox_add_read_path(path.as_ptr(), path.len() as u64);
    }
    Ok(Value::Nil)
}

/// Add a path to the write paths list.
///
/// Callable from Simple as: `rt_sandbox_add_write_path(path)`
pub fn rt_sandbox_add_write_path_fn(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => {
            return Err(CompileError::runtime(
                "rt_sandbox_add_write_path: path must be a string",
            ))
        }
    };
    unsafe {
        rt_sandbox_add_write_path(path.as_ptr(), path.len() as u64);
    }
    Ok(Value::Nil)
}

/// Apply the configured sandbox to the current process.
///
/// Callable from Simple as: `rt_sandbox_apply()`
///
/// Returns true on success, false on failure.
pub fn rt_sandbox_apply_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let result = rt_sandbox_apply();
    Ok(Value::Bool(result))
}

/// Cleanup network rules (Linux only, no-op on other platforms).
///
/// Callable from Simple as: `rt_sandbox_cleanup()`
pub fn rt_sandbox_cleanup_fn(_args: &[Value]) -> Result<Value, CompileError> {
    rt_sandbox_cleanup();
    Ok(Value::Nil)
}

/// Check if sandbox is currently configured (has any non-default settings).
///
/// Callable from Simple as: `rt_sandbox_is_configured()`
pub fn rt_sandbox_is_configured_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let result = rt_sandbox_is_configured();
    Ok(Value::Bool(result))
}

/// Get the current CPU time limit in seconds, or 0 if not set.
///
/// Callable from Simple as: `rt_sandbox_get_cpu_time()`
pub fn rt_sandbox_get_cpu_time_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let result = rt_sandbox_get_cpu_time();
    Ok(Value::Int(result as i64))
}

/// Get the current memory limit in bytes, or 0 if not set.
///
/// Callable from Simple as: `rt_sandbox_get_memory()`
pub fn rt_sandbox_get_memory_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let result = rt_sandbox_get_memory();
    Ok(Value::Int(result as i64))
}

/// Get the current network mode.
///
/// Callable from Simple as: `rt_sandbox_get_network_mode()`
///
/// Returns: 0 = Full, 1 = None, 2 = AllowList, 3 = BlockList
pub fn rt_sandbox_get_network_mode_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let result = rt_sandbox_get_network_mode();
    Ok(Value::Int(result as i64))
}

/// Get the current filesystem mode.
///
/// Callable from Simple as: `rt_sandbox_get_fs_mode()`
///
/// Returns: 0 = Full, 1 = ReadOnly, 2 = Restricted, 3 = Overlay
pub fn rt_sandbox_get_fs_mode_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let result = rt_sandbox_get_fs_mode();
    Ok(Value::Int(result as i64))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sandbox_reset() {
        let result = rt_sandbox_reset_fn(&[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_sandbox_is_configured_default() {
        // Reset first to ensure clean state
        rt_sandbox_reset_fn(&[]).unwrap();
        let result = rt_sandbox_is_configured_fn(&[]).unwrap();
        // Default state should not be configured
        assert_eq!(result, Value::Bool(false));
    }

    #[test]
    fn test_sandbox_set_cpu_time() {
        rt_sandbox_reset_fn(&[]).unwrap();
        let result = rt_sandbox_set_cpu_time_fn(&[Value::Int(60)]);
        assert!(result.is_ok());

        // Check it was set
        let cpu_time = rt_sandbox_get_cpu_time_fn(&[]).unwrap();
        assert_eq!(cpu_time, Value::Int(60));

        // Should be configured now
        let configured = rt_sandbox_is_configured_fn(&[]).unwrap();
        assert_eq!(configured, Value::Bool(true));
    }

    #[test]
    fn test_sandbox_network_mode() {
        rt_sandbox_reset_fn(&[]).unwrap();

        // Default should be Full (0)
        let mode = rt_sandbox_get_network_mode_fn(&[]).unwrap();
        assert_eq!(mode, Value::Int(0));

        // Disable network should set to None (1)
        rt_sandbox_disable_network_fn(&[]).unwrap();
        let mode = rt_sandbox_get_network_mode_fn(&[]).unwrap();
        assert_eq!(mode, Value::Int(1));
    }
}
