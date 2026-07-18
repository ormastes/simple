//! System operations extern functions
//!
//! Functions for accessing system-level information (command-line args, environment, etc.).

use crate::error::CompileError;
use crate::value::Value;
use std::collections::VecDeque;
use std::io::Read;
use std::process::Child;

fn clear_simple_child_stack_env(command: &mut std::process::Command) {
    command.env_remove("_SIMPLE_STACK_SET");
}

#[cfg(unix)]
fn configure_timeout_child_process_group(command: &mut std::process::Command) {
    use std::os::unix::process::CommandExt;

    unsafe {
        command.pre_exec(|| {
            if libc::setpgid(0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
}

#[cfg(not(unix))]
fn configure_timeout_child_process_group(_command: &mut std::process::Command) {}

const OUTPUT_TRUNCATION_PREFIX: &str = "\n[output truncated: ";
const POST_TIMEOUT_DRAIN_GRACE: std::time::Duration = std::time::Duration::from_millis(100);

struct BoundedOutputReader {
    handle: std::thread::JoinHandle<()>,
    output: std::sync::mpsc::Receiver<Vec<u8>>,
}

fn read_bounded<R: Read>(mut reader: R, max_bytes: usize) -> Vec<u8> {
    let head_len = (max_bytes + 1) / 2;
    let tail_len = max_bytes - head_len;
    // Allocate only as output arrives; a hostile caller can request an enormous
    // limit and must not force that allocation before the child writes anything.
    let mut head = Vec::new();
    let mut tail: VecDeque<u8> = VecDeque::new();
    let mut total = 0usize;
    let mut chunk = [0u8; 8192];

    while let Ok(count) = reader.read(&mut chunk) {
        if count == 0 {
            break;
        }
        total = total.saturating_add(count);
        let head_count = (head_len - head.len()).min(count);
        head.extend_from_slice(&chunk[..head_count]);
        if tail_len == 0 || head_count == count {
            continue;
        }
        let rest = &chunk[head_count..count];
        let overflow = tail.len().saturating_add(rest.len()).saturating_sub(tail_len);
        tail.drain(..overflow.min(tail.len()));
        let rest_start = rest.len().saturating_sub(tail_len);
        tail.extend(&rest[rest_start..]);
        while tail.len() > tail_len {
            tail.pop_front();
        }
    }

    if total <= max_bytes {
        head.extend(tail);
        return head;
    }

    let marker = format!("{OUTPUT_TRUNCATION_PREFIX}{} bytes omitted]\n", total - max_bytes);
    head.extend_from_slice(marker.as_bytes());
    head.extend(tail);
    head
}

fn spawn_bounded_output_reader<R: Read + Send + 'static>(
    reader: Option<R>,
    max_bytes: usize,
) -> Option<BoundedOutputReader> {
    reader.map(|pipe| {
        let (sender, output) = std::sync::mpsc::channel();
        let handle = std::thread::spawn(move || {
            let _ = sender.send(read_bounded(pipe, max_bytes));
        });
        BoundedOutputReader { handle, output }
    })
}

fn receive_bounded_output(output: std::sync::mpsc::Receiver<Vec<u8>>, bounded_wait: bool) -> Vec<u8> {
    if bounded_wait {
        output.recv_timeout(POST_TIMEOUT_DRAIN_GRACE).unwrap_or_default()
    } else {
        output.recv().unwrap_or_default()
    }
}

fn finish_bounded_output_reader(reader: Option<BoundedOutputReader>, bounded_wait: bool) -> Vec<u8> {
    let Some(reader) = reader else {
        return Vec::new();
    };
    if !bounded_wait {
        let _ = reader.handle.join();
    }
    receive_bounded_output(reader.output, bounded_wait)
}

fn finish_child_output_bounded(mut child: Child, timeout_ms: i64, max_output_bytes: usize) -> (Vec<u8>, Vec<u8>, i64) {
    let stdout_reader = spawn_bounded_output_reader(child.stdout.take(), max_output_bytes);
    let stderr_reader = spawn_bounded_output_reader(child.stderr.take(), max_output_bytes);
    let deadline = std::time::Instant::now().checked_add(std::time::Duration::from_millis(timeout_ms.max(0) as u64));

    let mut timed_out = false;
    let mut aborted = false;
    let mut status = None;
    loop {
        if status.is_none() {
            match child.try_wait() {
                Ok(Some(exit_status)) => status = Some(exit_status),
                Ok(None) if timeout_ms <= 0 => status = child.wait().ok(),
                Ok(None) => {}
                Err(_) => {
                    aborted = true;
                    let _ = child.kill();
                    let _ = child.wait();
                    break;
                }
            }
        }
        let readers_finished = stdout_reader.as_ref().is_none_or(|reader| reader.handle.is_finished())
            && stderr_reader.as_ref().is_none_or(|reader| reader.handle.is_finished());
        if status.is_some() && readers_finished {
            break;
        }
        if timeout_ms > 0 && deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            timed_out = true;
            #[cfg(unix)]
            {
                let rc = unsafe { libc::kill(-(child.id() as i32), libc::SIGKILL) };
                if rc != 0 {
                    let _ = child.kill();
                }
            }
            #[cfg(not(unix))]
            let _ = child.kill();
            if status.is_none() {
                let _ = child.wait();
            }
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }

    let bounded_drain = timed_out || aborted;
    let stdout = finish_bounded_output_reader(stdout_reader, bounded_drain);
    let mut stderr = finish_bounded_output_reader(stderr_reader, bounded_drain);
    if timed_out {
        if !stderr.is_empty() {
            stderr.push(b'\n');
        }
        stderr.extend_from_slice(b"Process timed out");
    }
    (
        stdout,
        stderr,
        if timed_out {
            -1
        } else {
            status.and_then(|status| status.code()).unwrap_or(-1) as i64
        },
    )
}

fn finish_child_output_with_timeout(mut child: Child, timeout_ms: i64) -> Result<(String, String, i64), ()> {
    let stdout_handle = child.stdout.take().map(|mut pipe| {
        std::thread::spawn(move || {
            let mut buf = String::new();
            let _ = pipe.read_to_string(&mut buf);
            buf
        })
    });
    let stderr_handle = child.stderr.take().map(|mut pipe| {
        std::thread::spawn(move || {
            let mut buf = String::new();
            let _ = pipe.read_to_string(&mut buf);
            buf
        })
    });

    let timeout = std::time::Duration::from_millis(timeout_ms as u64);
    let start = std::time::Instant::now();
    let poll_interval = std::time::Duration::from_millis(10);

    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    break Err(());
                }
                std::thread::sleep(poll_interval);
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(());
            }
        }
    };

    let stdout = stdout_handle
        .map(|handle| handle.join().unwrap_or_default())
        .unwrap_or_default();
    let stderr = stderr_handle
        .map(|handle| handle.join().unwrap_or_default())
        .unwrap_or_default();

    match status {
        Ok(exit_status) => Ok((stdout, stderr, exit_status.code().unwrap_or(-1) as i64)),
        Err(()) => {
            let stderr = if stderr.is_empty() {
                "Process timed out".to_string()
            } else {
                format!("{stderr}\nProcess timed out")
            };
            Ok((stdout, stderr, -1))
        }
    }
}
use crate::value_bridge::runtime_to_value;

use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    /// Map of spawned child processes by PID for rt_process_spawn_async/rt_process_wait
    static ref SPAWNED_PROCESSES: Mutex<HashMap<i64, std::process::Child>> = Mutex::new(HashMap::new());
}
use simple_runtime::value::{
    rt_env_all as sffi_env_all, rt_env_cwd as sffi_env_cwd, rt_env_exists as sffi_env_exists,
    rt_env_get as sffi_env_get, rt_env_get_i64 as sffi_env_get_i64, rt_env_home as sffi_env_home,
    rt_lexer_source_set as sffi_lexer_source_set, rt_lexer_source_slice as sffi_lexer_source_slice,
    rt_env_remove as sffi_env_remove, rt_env_set as sffi_env_set, rt_env_temp as sffi_env_temp,
    rt_set_debug_mode as sffi_set_debug_mode, rt_set_macro_trace as sffi_set_macro_trace,
    rt_platform_name as sffi_platform_name, rt_term_enable_ansi as sffi_term_enable_ansi,
};
use simple_runtime::value::sffi::config::{
    rt_is_debug_mode_enabled as sffi_is_debug_mode_enabled, rt_is_macro_trace_enabled as sffi_is_macro_trace_enabled,
};

/// Get command-line arguments
///
/// Callable from Simple as: `sys_get_args()`
///
/// # Arguments
/// * `args` - Evaluated arguments (none expected)
///
/// # Returns
/// * Array of strings representing command-line arguments
pub fn sys_get_args(_args: &[Value]) -> Result<Value, CompileError> {
    // Get command line arguments from runtime SFFI (unified approach)
    use crate::value_bridge::runtime_to_value;
    use simple_runtime::value::rt_get_args;

    let runtime_array = rt_get_args();
    let value = runtime_to_value(runtime_array);

    Ok(value)
}

/// Exit the process with a status code
///
/// Callable from Simple as: `sys_exit(code)`
///
/// This is identical to the `exit()` function but with `sys_` prefix
/// for consistency with other system operations.
///
/// # Arguments
/// * `args` - Evaluated arguments [optional exit_code]
///
/// # Returns
/// * Never returns - terminates the process
pub fn sys_exit(args: &[Value]) -> Result<Value, CompileError> {
    let code = args.first().map(|v| v.as_int()).transpose()?.unwrap_or(0) as i32;
    std::process::exit(code);
}

/// Set an environment variable
///
/// Callable from Simple as: `rt_env_set(key, value)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String, value: String]
///
/// # Returns
/// * Bool indicating success
pub fn rt_env_set(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_env_set requires 2 arguments (key, value)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_env_set: key must be a string")),
    };
    let value = match &args[1] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_env_set: value must be a string")),
    };

    unsafe {
        let result = sffi_env_set(key.as_ptr(), key.len() as u64, value.as_ptr(), value.len() as u64);
        Ok(Value::Bool(result))
    }
}

/// Get an environment variable
///
/// Callable from Simple as: `rt_env_get(key)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String]
///
/// # Returns
/// * String value of the environment variable
pub fn rt_env_get(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_env_get requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_env_get: key must be a string")),
    };

    unsafe {
        let result = sffi_env_get(key.as_ptr(), key.len() as u64);
        Ok(runtime_to_value(result))
    }
}

pub fn rt_lexer_source_set(args: &[Value]) -> Result<Value, CompileError> {
    let Some(Value::Str(source)) = args.first() else {
        return Err(CompileError::runtime("rt_lexer_source_set requires a text source"));
    };
    Ok(Value::Bool(unsafe {
        sffi_lexer_source_set(source.as_ptr(), source.len() as u64)
    }))
}

pub fn rt_lexer_source_slice(args: &[Value]) -> Result<Value, CompileError> {
    let (Some(Value::Int(start)), Some(Value::Int(end))) = (args.first(), args.get(1)) else {
        return Err(CompileError::runtime(
            "rt_lexer_source_slice requires integer start and end",
        ));
    };
    Ok(runtime_to_value(sffi_lexer_source_slice(*start, *end)))
}

/// Get an environment variable parsed as i64.
pub fn rt_env_get_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_env_get_i64 requires 2 arguments (key, default)",
        ));
    }

    let key = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_env_get_i64: key must be a string")),
    };
    let default_value = args[1].as_int()?;

    unsafe {
        Ok(Value::Int(sffi_env_get_i64(
            key.as_ptr(),
            key.len() as u64,
            default_value,
        )))
    }
}

/// Get an environment variable parsed as bool.
pub fn sys_env_bool(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("sys_env_bool requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s,
        _ => return Err(CompileError::runtime("sys_env_bool: key must be a string")),
    };
    let value = std::env::var(key.as_str()).unwrap_or_default().to_ascii_lowercase();
    Ok(Value::Bool(matches!(value.as_str(), "1" | "true" | "yes" | "on")))
}

/// Check if an environment variable exists
///
/// Callable from Simple as: `rt_env_exists(key)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String]
///
/// # Returns
/// * Bool indicating if the variable exists
pub fn rt_env_exists(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_env_exists requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_env_exists: key must be a string")),
    };

    unsafe {
        let result = sffi_env_exists(key.as_ptr(), key.len() as u64);
        Ok(Value::Bool(result))
    }
}

/// Remove an environment variable
///
/// Callable from Simple as: `rt_env_remove(key)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String]
///
/// # Returns
/// * Bool indicating success
pub fn rt_env_remove(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_env_remove requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_env_remove: key must be a string")),
    };

    unsafe {
        let result = sffi_env_remove(key.as_ptr(), key.len() as u64);
        Ok(Value::Bool(result))
    }
}

/// Get all environment variables
///
/// Callable from Simple as: `rt_env_all()`
///
/// # Returns
/// * Array of (key, value) tuples
pub fn rt_env_all(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = sffi_env_all();
        Ok(runtime_to_value(result))
    }
}

/// Get home directory
///
/// Callable from Simple as: `rt_env_home()`
///
/// # Returns
/// * String path to home directory
pub fn rt_env_home(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = sffi_env_home();
        // Return raw RuntimeValue as i64 for SFFI interop
        Ok(Value::Int(result.to_raw() as i64))
    }
}

/// Get temp directory
///
/// Callable from Simple as: `rt_env_temp()`
///
/// # Returns
/// * String path to temp directory
pub fn rt_env_temp(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = sffi_env_temp();
        // Return raw RuntimeValue as i64 for SFFI interop
        Ok(Value::Int(result.to_raw() as i64))
    }
}

/// Get current working directory
///
/// Callable from Simple as: `rt_env_cwd()`
///
/// # Returns
/// * String path to current working directory
pub fn rt_env_cwd(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = sffi_env_cwd();
        Ok(runtime_to_value(result))
    }
}

/// Enable or disable macro trace mode
///
/// Callable from Simple as: `rt_set_macro_trace(enabled)`
///
/// # Arguments
/// * `args` - Evaluated arguments [enabled: Bool]
///
/// # Returns
/// * Nil
pub fn rt_set_macro_trace(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => false,
    };
    sffi_set_macro_trace(enabled);
    Ok(Value::Nil)
}

/// Enable or disable debug mode
///
/// Callable from Simple as: `rt_set_debug_mode(enabled)`
///
/// # Arguments
/// * `args` - Evaluated arguments [enabled: Bool]
///
/// # Returns
/// * Nil
pub fn rt_set_debug_mode(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => false,
    };
    sffi_set_debug_mode(enabled);
    Ok(Value::Nil)
}

/// Check if macro trace is enabled
///
/// Callable from Simple as: `rt_is_macro_trace_enabled()`
///
/// # Returns
/// * Bool - true if macro trace is enabled
pub fn rt_is_macro_trace_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(sffi_is_macro_trace_enabled()))
}

/// Check if debug mode is enabled
///
/// Callable from Simple as: `rt_is_debug_mode_enabled()`
///
/// # Returns
/// * Bool - true if debug mode is enabled
pub fn rt_is_debug_mode_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(sffi_is_debug_mode_enabled()))
}

/// Run a command and capture output
///
/// Callable from Simple as: `rt_process_run(cmd, args)`
///
/// Implemented directly in the interpreter (not via SFFI) to return proper
/// Value::Tuple with Value::Str elements. The SFFI path via runtime_to_value
/// converts heap objects (strings, tuples) to opaque Value::Int pointers,
/// breaking tuple destructuring in interpreted code.
///
/// # Returns
/// * Tuple of (stdout: String, stderr: String, exit_code: Int)
pub fn rt_process_run(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_process_run requires 2 arguments (cmd, args)"));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_process_run: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.as_ref().clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run: args must be an array of strings",
            ))
        }
    };

    let mut command = std::process::Command::new(&*cmd);
    clear_simple_child_stack_env(&mut command);
    let output = command.args(&cmd_args).stdin(std::process::Stdio::null()).output();

    match output {
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            let stderr = String::from_utf8_lossy(&out.stderr).to_string();
            let exit_code = out.status.code().unwrap_or(-1) as i64;
            Ok(Value::Tuple(vec![
                Value::text(stdout),
                Value::text(stderr),
                Value::Int(exit_code),
            ]))
        }
        Err(_) => Ok(Value::Tuple(vec![
            Value::text(String::new()),
            Value::text(String::new()),
            Value::Int(-1),
        ])),
    }
}

/// Run a foreground command with inherited stdin/stdout/stderr.
pub fn rt_process_run_inherit(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_process_run_inherit requires 2 arguments (cmd, args)",
        ));
    }
    let cmd = match &args[0] {
        Value::Str(value) => value.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_process_run_inherit: cmd must be a string")),
    };
    let cmd_args = match &args[1] {
        Value::Array(values) => values
            .iter()
            .filter_map(|value| match value {
                Value::Str(text) => Some(text.as_ref().clone()),
                _ => None,
            })
            .collect::<Vec<_>>(),
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_inherit: args must be an array of strings",
            ))
        }
    };
    let mut command = std::process::Command::new(&*cmd);
    clear_simple_child_stack_env(&mut command);
    let code = command
        .args(cmd_args)
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit())
        .status()
        .ok()
        .and_then(|status| status.code())
        .unwrap_or(-1) as i64;
    Ok(Value::Int(code))
}

/// Run a command synchronously and return only the exit code.
///
/// Callable from Simple as: `rt_process_execute(cmd, args)`
///
/// # Returns
/// * Int - exit code (0 = success, -1 = error)
pub fn rt_process_execute(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_process_execute requires 2 arguments (cmd, args)",
        ));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_process_execute: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.as_ref().clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_execute: args must be an array of strings",
            ))
        }
    };

    let mut command = std::process::Command::new(&*cmd);
    clear_simple_child_stack_env(&mut command);
    let status = command
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    match status {
        Ok(s) => Ok(Value::Int(s.code().unwrap_or(-1) as i64)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// Run a command with timeout and capture output
///
/// Callable from Simple as: `rt_process_run_timeout(cmd, args, timeout_ms)`
///
/// Implemented directly in the interpreter (not via SFFI) to return proper
/// Value::Tuple with Value::Str elements, avoiding the runtime_to_value bug.
///
/// # Arguments
/// * `args` - Evaluated arguments [cmd: String, args: List<String>, timeout_ms: Int]
///
/// # Returns
/// * Tuple of (stdout: String, stderr: String, exit_code: Int) where exit_code=-1 on timeout
pub fn rt_process_run_timeout(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_process_run_timeout requires 3 arguments (cmd, args, timeout_ms)",
        ));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_process_run_timeout: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.as_ref().clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_timeout: args must be an array of strings",
            ))
        }
    };

    let timeout_ms = match &args[2] {
        Value::Int(n) => *n,
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_timeout: timeout_ms must be an integer",
            ))
        }
    };

    let mut command = std::process::Command::new(&*cmd);
    clear_simple_child_stack_env(&mut command);
    let mut child = match command
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => {
            return Ok(Value::Tuple(vec![
                Value::text(String::new()),
                Value::text(String::new()),
                Value::Int(-1),
            ]));
        }
    };

    match finish_child_output_with_timeout(child, timeout_ms) {
        Ok((stdout, stderr, exit_code)) => Ok(Value::Tuple(vec![
            Value::text(stdout),
            Value::text(stderr),
            Value::Int(exit_code),
        ])),
        Err(()) => Ok(Value::Tuple(vec![
            Value::text(String::new()),
            Value::text("Process timed out".to_string()),
            Value::Int(-1),
        ])),
    }
}

/// Run a command while retaining at most `max_output_bytes` from each stream.
///
/// Truncated streams contain their retained head and tail separated by
/// `\n[output truncated: N bytes omitted]\n`; the marker is outside the byte budget.
pub fn rt_process_run_bounded(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Err(CompileError::runtime(
            "rt_process_run_bounded requires 4 arguments (cmd, args, timeout_ms, max_output_bytes)",
        ));
    }
    let cmd = match &args[0] {
        Value::Str(value) => value.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_process_run_bounded: cmd must be a string")),
    };
    let cmd_args = match &args[1] {
        Value::Array(values) => values
            .iter()
            .filter_map(|value| match value {
                Value::Str(value) => Some(value.as_ref().clone()),
                _ => None,
            })
            .collect::<Vec<_>>(),
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_bounded: args must be an array of strings",
            ))
        }
    };
    let timeout_ms = match args[2] {
        Value::Int(value) => value,
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_bounded: timeout_ms must be an integer",
            ))
        }
    };
    let max_output_bytes = match args[3] {
        Value::Int(value) if value >= 0 => usize::try_from(value).unwrap_or(usize::MAX),
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_bounded: max_output_bytes must be a non-negative integer",
            ))
        }
    };

    let mut command = std::process::Command::new(&*cmd);
    clear_simple_child_stack_env(&mut command);
    configure_timeout_child_process_group(&mut command);
    let child = match command
        .args(cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => {
            return Ok(Value::Tuple(vec![
                Value::text(String::new()),
                Value::text(String::new()),
                Value::Int(-1),
            ]))
        }
    };
    let (stdout, stderr, exit_code) = finish_child_output_bounded(child, timeout_ms, max_output_bytes);
    Ok(Value::Tuple(vec![
        Value::text(String::from_utf8_lossy(&stdout).into_owned()),
        Value::text(String::from_utf8_lossy(&stderr).into_owned()),
        Value::Int(exit_code),
    ]))
}

/// Spawn a process asynchronously and return its PID
///
/// Callable from Simple as: `rt_process_spawn_async(cmd, args)`
///
/// # Arguments
/// * `args` - Evaluated arguments [cmd: String, args: List<String>]
///
/// # Returns
/// * Int - process ID (PID), or -1 on failure
pub fn rt_process_spawn_async(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_process_spawn_async requires 2 arguments (cmd, args)",
        ));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
        _ => return Err(CompileError::runtime("rt_process_spawn_async: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.as_ref().clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_spawn_async: args must be an array of strings",
            ))
        }
    };

    let mut command = std::process::Command::new(&*cmd);
    clear_simple_child_stack_env(&mut command);
    match command
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit())
        .spawn()
    {
        Ok(child) => {
            let pid = child.id() as i64;
            // Store the child process for later wait
            SPAWNED_PROCESSES.lock().unwrap().insert(pid, child);
            Ok(Value::Int(pid))
        }
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// Wait for a spawned process to complete
///
/// Callable from Simple as: `rt_process_wait(pid, timeout_ms)`
///
/// # Arguments
/// * `args` - Evaluated arguments [pid: Int, optional timeout_ms: Int]
///
/// # Returns
/// * Int - exit code, -2 on timeout, or -1 on failure
pub fn rt_process_wait(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_process_wait requires 1 argument (pid)"));
    }

    let pid = match &args[0] {
        Value::Int(n) => *n,
        _ => return Err(CompileError::runtime("rt_process_wait: pid must be an integer")),
    };

    let timeout_ms = match args.get(1) {
        Some(Value::Int(n)) => *n,
        Some(_) => return Err(CompileError::runtime("rt_process_wait: timeout must be an integer")),
        None => 0,
    };

    if timeout_ms > 0 {
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(timeout_ms as u64);
        loop {
            let poll = {
                let mut processes = SPAWNED_PROCESSES.lock().unwrap();
                match processes.get_mut(&pid) {
                    Some(child) => child.try_wait(),
                    None => return Ok(Value::Int(-1)),
                }
            };
            match poll {
                Ok(Some(status)) => {
                    SPAWNED_PROCESSES.lock().unwrap().remove(&pid);
                    return Ok(Value::Int(status.code().unwrap_or(-1) as i64));
                }
                Ok(None) if std::time::Instant::now() >= deadline => return Ok(Value::Int(-2)),
                Ok(None) => std::thread::sleep(std::time::Duration::from_millis(10)),
                Err(_) => {
                    SPAWNED_PROCESSES.lock().unwrap().remove(&pid);
                    return Ok(Value::Int(-1));
                }
            }
        }
    }

    let mut processes = SPAWNED_PROCESSES.lock().unwrap();
    match processes.remove(&pid) {
        Some(mut child) => match child.wait() {
            Ok(status) => Ok(Value::Int(status.code().unwrap_or(-1) as i64)),
            Err(_) => Ok(Value::Int(-1)),
        },
        None => {
            // Process not found in our map - may have already been waited on
            Ok(Value::Int(-1))
        }
    }
}

/// Check if a previously spawned async process is still running.
///
/// Callable from Simple as: `rt_process_is_running(pid: i64) -> bool`
///
/// # Returns
/// * Bool: true if the process is still running, false if exited or not found
pub fn rt_process_is_running(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_process_is_running requires 1 argument (pid)"));
    }
    let pid = match &args[0] {
        Value::Int(n) => *n,
        _ => return Err(CompileError::runtime("rt_process_is_running: pid must be an integer")),
    };
    let mut processes = SPAWNED_PROCESSES.lock().unwrap();
    match processes.get_mut(&pid) {
        Some(child) => match child.try_wait() {
            Ok(None) => Ok(Value::Bool(true)), // still running
            _ => Ok(Value::Bool(false)),       // exited or error
        },
        None => Ok(Value::Bool(false)), // not tracked
    }
}

/// Kill a previously spawned async process.
///
/// Callable from Simple as: `rt_process_kill(pid: i64) -> bool`
///
/// # Returns
/// * Bool: true if killed successfully, false otherwise
pub fn rt_process_kill(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_process_kill requires 1 argument (pid)"));
    }
    let pid = match &args[0] {
        Value::Int(n) => *n,
        _ => return Err(CompileError::runtime("rt_process_kill: pid must be an integer")),
    };
    let child = SPAWNED_PROCESSES.lock().unwrap().remove(&pid);
    match child {
        Some(mut child) => {
            let killed = child.kill().is_ok();
            let reaped = child.wait().is_ok();
            Ok(Value::Bool(killed && reaped))
        }
        None => Ok(Value::Bool(false)),
    }
}

/// Get platform name
///
/// Callable from Simple as: `rt_platform_name()`
///
/// # Returns
/// * String: "linux", "macos", "windows", etc.
pub fn rt_platform_name(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = sffi_platform_name();
        Ok(runtime_to_value(result))
    }
}

/// Enable ANSI virtual terminal processing on Windows
///
/// Callable from Simple as: `rt_term_enable_ansi()`
///
/// # Returns
/// * Bool: always true
pub fn rt_term_enable_ansi(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = sffi_term_enable_ansi();
        Ok(runtime_to_value(result))
    }
}

/// Get terminal size (columns, rows)
///
/// Callable from Simple as: `rt_term_get_size()`
///
/// # Returns
/// * Tuple(Int, Int): (columns, rows), falls back to (80, 24) if detection fails
pub fn rt_term_get_size(_args: &[Value]) -> Result<Value, CompileError> {
    let (cols, rows) = get_terminal_size_impl();
    Ok(Value::Tuple(vec![Value::Int(cols as i64), Value::Int(rows as i64)]))
}

/// Platform-specific terminal size detection
fn get_terminal_size_impl() -> (i32, i32) {
    #[cfg(unix)]
    {
        unsafe {
            let mut ws: libc::winsize = std::mem::zeroed();
            if libc::ioctl(libc::STDOUT_FILENO, libc::TIOCGWINSZ, &mut ws) == 0 && ws.ws_col > 0 && ws.ws_row > 0 {
                return (ws.ws_col as i32, ws.ws_row as i32);
            }
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::io::AsRawHandle;
        extern "system" {
            fn GetConsoleScreenBufferInfo(handle: isize, info: *mut ConsoleScreenBufferInfo) -> i32;
        }
        #[repr(C)]
        struct Coord {
            x: i16,
            y: i16,
        }
        #[repr(C)]
        struct SmallRect {
            left: i16,
            top: i16,
            right: i16,
            bottom: i16,
        }
        #[repr(C)]
        struct ConsoleScreenBufferInfo {
            size: Coord,
            cursor_position: Coord,
            attributes: u16,
            window: SmallRect,
            maximum_window_size: Coord,
        }
        let handle = std::io::stdout().as_raw_handle() as isize;
        unsafe {
            let mut info: ConsoleScreenBufferInfo = std::mem::zeroed();
            if GetConsoleScreenBufferInfo(handle, &mut info) != 0 {
                let cols = info.window.right - info.window.left + 1;
                let rows = info.window.bottom - info.window.top + 1;
                if cols > 0 && rows > 0 {
                    return (cols as i32, rows as i32);
                }
            }
        }
    }
    // Fallback
    (80, 24)
}

/// Exit the process with given exit code
///
/// Callable from Simple as: `rt_exit(code)`
///
/// # Arguments
/// * `args` - Evaluated arguments [code: Int]
pub fn rt_exit(args: &[Value]) -> Result<Value, CompileError> {
    let code = match args.first() {
        Some(Value::Int(n)) => *n as i32,
        _ => 1,
    };
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[cfg(unix)]
    #[test]
    fn process_wait_timeout_keeps_child_tracked_until_killed() {
        let pid = rt_process_spawn_async(&[
            Value::text("/bin/sh".to_string()),
            Value::Array(Arc::new(vec![
                Value::text("-c".to_string()),
                Value::text("sleep 30".to_string()),
            ])),
        ])
        .expect("spawn")
        .as_int()
        .expect("pid");
        assert!(pid > 0);
        assert_eq!(
            rt_process_wait(&[Value::Int(pid), Value::Int(10)]).unwrap(),
            Value::Int(-2)
        );
        assert_eq!(rt_process_is_running(&[Value::Int(pid)]).unwrap(), Value::Bool(true));
        assert_eq!(rt_process_kill(&[Value::Int(pid)]).unwrap(), Value::Bool(true));
        assert_eq!(rt_process_is_running(&[Value::Int(pid)]).unwrap(), Value::Bool(false));
    }

    #[test]
    fn test_sys_get_args() {
        // Should return an array
        let result = sys_get_args(&[]);
        assert!(result.is_ok());
        // Value type depends on runtime implementation
    }

    #[cfg(unix)]
    #[test]
    fn test_process_run_clears_simple_stack_env_for_children() {
        unsafe {
            std::env::set_var("_SIMPLE_STACK_SET", "1");
        }
        let result = rt_process_run(&[
            Value::text("/bin/sh".to_string()),
            Value::Array(Arc::new(vec![
                Value::text("-c".to_string()),
                Value::text(
                    "if env | grep '^_SIMPLE_STACK_SET=' >/dev/null; then printf present; else printf unset; fi"
                        .to_string(),
                ),
            ])),
        ])
        .expect("rt_process_run should succeed");

        let Value::Tuple(parts) = result else {
            panic!("expected tuple result");
        };
        assert_eq!(parts.len(), 3);
        let Value::Str(stdout) = &parts[0] else {
            panic!("expected stdout string");
        };
        let Value::Int(exit_code) = parts[2] else {
            panic!("expected exit code int");
        };

        assert_eq!(stdout.as_str(), "unset");
        assert_eq!(exit_code, 0);
        unsafe {
            std::env::remove_var("_SIMPLE_STACK_SET");
        }
    }

    #[cfg(unix)]
    #[test]
    fn process_run_bounded_drains_flooding_streams_with_head_and_tail() {
        let result = rt_process_run_bounded(&[
            Value::text("/bin/sh".to_string()),
            Value::Array(Arc::new(vec![
                Value::text("-c".to_string()),
                Value::text(
                    "printf HEAD; head -c 10000 /dev/zero | tr '\\0' x; printf TAIL; printf HEAD >&2; head -c 10000 /dev/zero | tr '\\0' y >&2; printf TAIL >&2"
                        .to_string(),
                ),
            ])),
            Value::Int(5_000),
            Value::Int(64),
        ])
        .unwrap();
        let Value::Tuple(parts) = result else {
            panic!("expected tuple");
        };
        assert_eq!(parts[2], Value::Int(0));
        for part in &parts[..2] {
            let Value::Str(output) = part else {
                panic!("expected string");
            };
            assert!(output.starts_with("HEAD"));
            assert!(output.ends_with("TAIL"));
            assert!(output.contains("\n[output truncated: 9944 bytes omitted]\n"));
        }
    }

    #[cfg(unix)]
    #[test]
    fn process_run_bounded_timeout_kills_descendant_process_group() {
        let result = rt_process_run_bounded(&[
            Value::text("/bin/sh".to_string()),
            Value::Array(Arc::new(vec![
                Value::text("-c".to_string()),
                Value::text("sleep 30 & child=$!; printf '%s' \"$child\"".to_string()),
            ])),
            Value::Int(100),
            Value::Int(128),
        ])
        .unwrap();
        let Value::Tuple(parts) = result else {
            panic!("expected tuple");
        };
        assert_eq!(parts[2], Value::Int(-1));
        let Value::Str(stdout) = &parts[0] else {
            panic!("expected stdout string");
        };
        let Value::Str(stderr) = &parts[1] else {
            panic!("expected stderr string");
        };
        let descendant = stdout.parse::<i32>().expect("descendant pid");
        assert!(stderr.ends_with("Process timed out"));
        for _ in 0..100 {
            if unsafe { libc::kill(descendant, 0) } != 0 {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        panic!("descendant process {descendant} survived timeout cleanup");
    }

    #[test]
    fn bounded_output_timeout_does_not_wait_for_an_open_pipe() {
        let (sender, receiver) = std::sync::mpsc::channel();
        let started = std::time::Instant::now();
        assert!(receive_bounded_output(receiver, true).is_empty());
        assert!(started.elapsed() < std::time::Duration::from_millis(500));
        drop(sender);
    }

    #[test]
    fn lexer_source_slice_handler_preserves_owned_text() {
        assert_eq!(
            rt_lexer_source_set(&[Value::text("aéz".to_string())]).unwrap(),
            Value::Bool(true)
        );
        let saved = rt_lexer_source_slice(&[Value::Int(1), Value::Int(2)]).unwrap();
        assert_eq!(saved, Value::text("é".to_string()));
        assert_eq!(
            rt_lexer_source_set(&[Value::text("new".to_string())]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(saved, Value::text("é".to_string()));
        assert_eq!(
            rt_lexer_source_slice(&[Value::Int(0), Value::Int(3)]).unwrap(),
            Value::text("new".to_string())
        );
        assert_eq!(
            rt_lexer_source_slice(&[Value::Int(1), Value::Int(99)]).unwrap(),
            Value::Nil
        );
    }

    // Note: Can't test sys_exit() as it terminates the process
}
