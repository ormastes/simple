//! Process spawning and management FFI functions

use crate::value::RuntimeValue;
use std::os::unix::io::RawFd;

#[cfg(unix)]
use nix::unistd::{fork, ForkResult, execvp, setsid};
#[cfg(unix)]
use nix::sys::signal::{kill, Signal};
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
#[cfg(unix)]
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
#[cfg(unix)]
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
