//! Process management operations
//!
//! Provides native implementations for:
//! - Process spawning with inherited mmap regions
//! - Process lifecycle management (wait, is_alive, kill)
//! - Path resolution utilities

use super::super::RuntimeValue;

/// Spawn worker process with inherited mmap regions
///
/// Creates a child process that inherits all memory-mapped regions from the parent.
/// This is useful for worker processes that need access to shared memory.
///
/// # Arguments
/// * `worker_fn` - Function pointer to execute in child process
///
/// # Returns
/// Process ID (PID) of spawned child, or NIL on error
///
/// # Safety
/// This function uses `fork()` which has complex thread-safety implications.
/// It should only be called from single-threaded contexts or with proper
/// synchronization to ensure all threads are in a safe state.
#[no_mangle]
pub extern "C" fn native_spawn_worker(worker_fn: u64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{fork, pid_t};

        unsafe {
            let pid: pid_t = fork();

            if pid < 0 {
                // Fork failed
                return RuntimeValue::NIL;
            } else if pid == 0 {
                // Child process - execute worker function
                let func: extern "C" fn() -> i64 = std::mem::transmute(worker_fn as *const ());
                let exit_code = func();
                libc::exit(exit_code as i32);
            } else {
                // Parent process - return child PID
                return RuntimeValue::from_int(pid as i64);
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL // Not supported on non-Unix platforms
    }
}

/// Wait for process to complete
///
/// Blocks until the specified process terminates, then returns its exit code.
///
/// # Arguments
/// * `pid` - Process ID to wait for
///
/// # Returns
/// Exit code of process (0-255 for normal exit, -1 for abnormal termination)
#[no_mangle]
pub extern "C" fn native_process_wait(pid: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{pid_t, waitpid, WEXITSTATUS, WIFEXITED};

        unsafe {
            let mut status: i32 = 0;
            let result = waitpid(pid as pid_t, &mut status as *mut i32, 0);

            if result < 0 {
                return RuntimeValue::NIL;
            }

            // Extract exit code
            if WIFEXITED(status) {
                let exit_code = WEXITSTATUS(status);
                RuntimeValue::from_int(exit_code as i64)
            } else {
                RuntimeValue::from_int(-1) // Abnormal termination
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Check if process is still running
///
/// Uses the POSIX `kill()` system call with signal 0 to check process existence
/// without actually sending a signal.
///
/// # Arguments
/// * `pid` - Process ID to check
///
/// # Returns
/// True if process is alive, false otherwise
#[no_mangle]
pub extern "C" fn native_process_is_alive(pid: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{kill, pid_t};

        unsafe {
            // Signal 0 checks if process exists without sending a signal
            let result = kill(pid as pid_t, 0);
            RuntimeValue::from_bool(result == 0)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::FALSE
    }
}

/// Kill/terminate process
///
/// Sends SIGTERM to the specified process, requesting graceful termination.
/// The process may choose to ignore this signal or perform cleanup before exiting.
///
/// # Arguments
/// * `pid` - Process ID to kill
///
/// # Returns
/// NIL on success or error (both return NIL for simplicity)
#[no_mangle]
pub extern "C" fn native_process_kill(pid: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{kill, pid_t, SIGTERM};

        unsafe {
            let result = kill(pid as pid_t, SIGTERM);

            if result == 0 {
                RuntimeValue::NIL // Success
            } else {
                RuntimeValue::NIL // Error
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Extract string from RuntimeValue (heap pointer to RuntimeString)
unsafe fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    let ptr = val.as_heap_ptr() as *const super::super::collections::RuntimeString;
    if ptr.is_null() {
        return None;
    }

    // Get bytes from RuntimeString
    let s = &*ptr;
    let bytes = s.as_bytes();
    String::from_utf8(bytes.to_vec()).ok()
}

/// Create RuntimeString from Rust String
fn string_to_runtime_value(s: &str) -> RuntimeValue {
    super::super::collections::rt_string_new(s.as_ptr(), s.len() as u64)
}

// =============================================================================
// Path Resolution
// =============================================================================

/// Resolve relative path to absolute path
///
/// Converts a potentially relative path to an absolute filesystem path.
///
/// # Arguments
/// * `path` - File path (potentially relative)
///
/// # Returns
/// Absolute path as RuntimeValue
#[no_mangle]
pub extern "C" fn native_path_resolve(path: RuntimeValue) -> RuntimeValue {
    // Extract path string from RuntimeValue
    let path_str = match unsafe { runtime_value_to_string(path) } {
        Some(s) => s,
        None => return path, // Return as-is if not a valid string
    };

    // Resolve to absolute path
    let resolved = match std::path::Path::new(&path_str).canonicalize() {
        Ok(abs_path) => abs_path.to_string_lossy().to_string(),
        Err(_) => {
            // If canonicalize fails (path doesn't exist), try to resolve manually
            if std::path::Path::new(&path_str).is_absolute() {
                path_str
            } else {
                // Prepend current working directory
                match std::env::current_dir() {
                    Ok(cwd) => cwd.join(&path_str).to_string_lossy().to_string(),
                    Err(_) => path_str,
                }
            }
        }
    };

    string_to_runtime_value(&resolved)
}
