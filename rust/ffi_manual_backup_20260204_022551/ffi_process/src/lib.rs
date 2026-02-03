//! process module
//!
//! Process Execution FFI
//! 
//! Process execution, shell commands, and output capture.

use std::process::{Command, Stdio};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Run process and capture output (returns stdout\tstderr\texit_code)
#[no_mangle]
pub unsafe extern "C" fn rt_process_run(cmd: *const c_char, args: *const c_char) -> *mut c_char {
    let cmd_str = CStr::from_ptr(cmd as *const i8).to_string_lossy();
    let args_str = CStr::from_ptr(args as *const i8).to_string_lossy();
    let args_vec: Vec<&str> = if args_str.is_empty() {
        Vec::new()
    } else {
        args_str.split('\n').collect()
    };
    match Command::new(cmd_str.as_ref())
        .args(&args_vec)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
    {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let exit_code = output.status.code().unwrap_or(-1);
            let result = format!("{}\t{}\t{}", stdout, stderr, exit_code);
            CString::new(result).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Run process with timeout (timeout not yet implemented)
#[no_mangle]
pub unsafe extern "C" fn rt_process_run_timeout(cmd: *const c_char, args: *const c_char, _timeout_ms: i64) -> *mut c_char {
    // TODO: Implement timeout support
    // For now, just call rt_process_run
    rt_process_run(cmd, args)
}

/// Run process and get output (alias for rt_process_run)
#[no_mangle]
pub unsafe extern "C" fn rt_process_output(cmd: *const c_char, args: *const c_char) -> *mut c_char {
    rt_process_run(cmd, args)
}

/// Execute shell command and return stdout
#[no_mangle]
pub unsafe extern "C" fn rt_shell(cmd: *const c_char) -> *mut c_char {
    let cmd_str = CStr::from_ptr(cmd as *const i8).to_string_lossy();
    match Command::new("sh")
        .arg("-c")
        .arg(cmd_str.as_ref())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
    {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            CString::new(stdout).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Execute shell command and return exit code
#[no_mangle]
pub unsafe extern "C" fn rt_shell_exec(cmd: *const c_char) -> i64 {
    let cmd_str = CStr::from_ptr(cmd as *const i8).to_string_lossy();
    Command::new("sh")
        .arg("-c")
        .arg(cmd_str.as_ref())
        .status()
        .map(|s| s.code().unwrap_or(-1) as i64)
        .unwrap_or(-1)
}

/// Get current process ID
#[no_mangle]
pub extern "C" fn rt_getpid() -> i64 {
    std::process::id() as i64
}

