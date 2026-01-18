//! Process spawning and management FFI functions

use crate::value::RuntimeValue;
use std::os::unix::io::RawFd;

#[cfg(unix)]
use nix::sys::signal::{kill, Signal};
#[cfg(unix)]
use nix::unistd::{execvp, fork, setsid, ForkResult};
#[cfg(unix)]
use std::ffi::CString;

/// Spawn a process with PTY
/// Returns: process ID (pid), or -1 on error
#[no_mangle]
pub extern "C" fn native_process_spawn_with_pty(
    command: RuntimeValue,
    args: RuntimeValue,
    slave_fd: i64,
) -> RuntimeValue {
    #[cfg(unix)]
    {
        // Convert command to string
        let cmd = unsafe {
            if let Some(s) = runtime_value_to_string(command) {
                s
            } else {
                eprintln!("Failed to convert command to string");
                return RuntimeValue::from_int(-1);
            }
        };

        // Convert args array to Vec<String>
        let args_vec = unsafe {
            if let Some(v) = runtime_value_to_string_array(args) {
                v
            } else {
                eprintln!("Failed to convert args to string array");
                return RuntimeValue::from_int(-1);
            }
        };

        let slave = slave_fd as RawFd;

        // Fork the process
        match unsafe { fork() } {
            Ok(ForkResult::Parent { child }) => {
                // Parent: return child PID
                RuntimeValue::from_int(child.as_raw() as i64)
            }
            Ok(ForkResult::Child) => {
                // Child: setup PTY and exec
                unsafe {
                    // Create new session
                    let _ = setsid();

                    // Redirect stdin, stdout, stderr to PTY slave using libc
                    libc::dup2(slave, 0); // stdin
                    libc::dup2(slave, 1); // stdout
                    libc::dup2(slave, 2); // stderr

                    // Close the slave fd after dup2
                    libc::close(slave);

                    // Prepare command and args for execvp
                    let mut exec_args = vec![cmd.clone()];
                    exec_args.extend(args_vec);

                    let c_cmd = CString::new(cmd).expect("CString::new failed");
                    let c_args: Vec<CString> = exec_args
                        .iter()
                        .map(|s| CString::new(s.as_str()).expect("CString::new failed"))
                        .collect();

                    // Execute the command
                    let _ = execvp(&c_cmd, &c_args);

                    // If we reach here, exec failed
                    eprintln!("Failed to exec: {}", std::io::Error::last_os_error());
                    libc::exit(1);
                }
            }
            Err(e) => {
                eprintln!("Fork failed: {}", e);
                RuntimeValue::from_int(-1)
            }
        }
    }

    #[cfg(not(unix))]
    {
        eprintln!("Process spawning not supported on non-Unix platforms");
        RuntimeValue::from_int(-1)
    }
}

/// Send SIGTERM to a process
#[no_mangle]
pub extern "C" fn native_process_terminate(pid: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        use nix::unistd::Pid;

        let pid = Pid::from_raw(pid as i32);

        match kill(pid, Signal::SIGTERM) {
            Ok(_) => RuntimeValue::from_bool(true),
            Err(e) => {
                eprintln!("Terminate failed: {}", e);
                RuntimeValue::from_bool(false)
            }
        }
    }

    #[cfg(not(unix))]
    {
        RuntimeValue::from_bool(false)
    }
}

/// Helper to extract string from RuntimeValue
unsafe fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    let ptr = val.as_heap_ptr() as *const super::collections::RuntimeString;
    if ptr.is_null() {
        return None;
    }

    let s = &*ptr;
    let bytes = s.as_bytes();
    String::from_utf8(bytes.to_vec()).ok()
}

/// Helper to convert RuntimeValue array to Vec<String>
unsafe fn runtime_value_to_string_array(val: RuntimeValue) -> Option<Vec<String>> {
    if !val.is_heap() {
        return None;
    }

    let ptr = val.as_heap_ptr() as *const super::collections::RuntimeArray;
    if ptr.is_null() {
        return None;
    }

    let arr = &*ptr;
    let slice = arr.as_slice();
    let mut result = Vec::with_capacity(slice.len());

    for elem in slice {
        if let Some(s) = runtime_value_to_string(*elem) {
            result.push(s);
        } else {
            return None;
        }
    }

    Some(result)
}

// =============================================================================
// Command Execution API
// =============================================================================

/// Execute a command and wait for completion.
///
/// # Arguments
/// * `command` - Command to execute (e.g., "ls", "/usr/bin/simple")
/// * `args` - Array of string arguments
///
/// # Returns
/// Exit code of the process (0 for success, non-zero for failure, -1 for spawn error)
#[no_mangle]
pub extern "C" fn native_command_run(command: RuntimeValue, args: RuntimeValue) -> RuntimeValue {
    let cmd = unsafe {
        match runtime_value_to_string(command) {
            Some(s) => s,
            None => return RuntimeValue::from_int(-1),
        }
    };

    let args_vec = unsafe {
        match runtime_value_to_string_array(args) {
            Some(v) => v,
            None => Vec::new(),
        }
    };

    match std::process::Command::new(&cmd).args(&args_vec).status() {
        Ok(status) => RuntimeValue::from_int(status.code().unwrap_or(-1) as i64),
        Err(e) => {
            tracing::warn!("Failed to execute command '{}': {}", cmd, e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Execute a command and capture its stdout output.
///
/// # Arguments
/// * `command` - Command to execute
/// * `args` - Array of string arguments
///
/// # Returns
/// Tuple of (exit_code, stdout_string), or (-1, "") on error
#[no_mangle]
pub extern "C" fn native_command_output(command: RuntimeValue, args: RuntimeValue) -> RuntimeValue {
    let cmd = unsafe {
        match runtime_value_to_string(command) {
            Some(s) => s,
            None => return create_command_result(-1, ""),
        }
    };

    let args_vec = unsafe {
        match runtime_value_to_string_array(args) {
            Some(v) => v,
            None => Vec::new(),
        }
    };

    match std::process::Command::new(&cmd).args(&args_vec).output() {
        Ok(output) => {
            let exit_code = output.status.code().unwrap_or(-1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout);
            create_command_result(exit_code, &stdout)
        }
        Err(e) => {
            tracing::warn!("Failed to execute command '{}': {}", cmd, e);
            create_command_result(-1, &format!("Error: {}", e))
        }
    }
}

/// Execute a command with a timeout (in milliseconds).
///
/// # Arguments
/// * `command` - Command to execute
/// * `args` - Array of string arguments
/// * `timeout_ms` - Timeout in milliseconds
///
/// # Returns
/// Exit code, or -2 if timed out, -1 on error
#[no_mangle]
pub extern "C" fn native_command_run_timeout(
    command: RuntimeValue,
    args: RuntimeValue,
    timeout_ms: i64,
) -> RuntimeValue {
    let cmd = unsafe {
        match runtime_value_to_string(command) {
            Some(s) => s,
            None => return RuntimeValue::from_int(-1),
        }
    };

    let args_vec = unsafe {
        match runtime_value_to_string_array(args) {
            Some(v) => v,
            None => Vec::new(),
        }
    };

    let mut child = match std::process::Command::new(&cmd).args(&args_vec).spawn() {
        Ok(c) => c,
        Err(e) => {
            tracing::warn!("Failed to spawn command '{}': {}", cmd, e);
            return RuntimeValue::from_int(-1);
        }
    };

    let timeout = std::time::Duration::from_millis(timeout_ms as u64);

    match child.wait_timeout(timeout) {
        Ok(Some(status)) => RuntimeValue::from_int(status.code().unwrap_or(-1) as i64),
        Ok(None) => {
            // Timed out - kill the process
            let _ = child.kill();
            let _ = child.wait();
            RuntimeValue::from_int(-2) // Timeout indicator
        }
        Err(e) => {
            tracing::warn!("Failed to wait for command '{}': {}", cmd, e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Helper to create command result tuple (exit_code, output_string)
fn create_command_result(exit_code: i64, output: &str) -> RuntimeValue {
    // Create a tuple/array with [exit_code, output_string]
    let exit_val = RuntimeValue::from_int(exit_code);
    let output_val = super::collections::rt_string_new(output.as_ptr(), output.len() as u64);

    // Create array with two elements using rt_array_new and rt_array_push
    let arr = super::collections::rt_array_new(2);
    super::collections::rt_array_push(arr, exit_val);
    super::collections::rt_array_push(arr, output_val);
    arr
}

/// Trait extension for wait_timeout on Child
trait ChildExt {
    fn wait_timeout(&mut self, timeout: std::time::Duration) -> std::io::Result<Option<std::process::ExitStatus>>;
}

impl ChildExt for std::process::Child {
    fn wait_timeout(&mut self, timeout: std::time::Duration) -> std::io::Result<Option<std::process::ExitStatus>> {
        use std::thread;
        use std::time::Instant;

        let start = Instant::now();
        let poll_interval = std::time::Duration::from_millis(10);

        loop {
            match self.try_wait()? {
                Some(status) => return Ok(Some(status)),
                None => {
                    if start.elapsed() >= timeout {
                        return Ok(None);
                    }
                    thread::sleep(poll_interval);
                }
            }
        }
    }
}
