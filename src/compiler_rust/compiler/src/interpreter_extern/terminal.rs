//! Terminal operations extern functions
//!
//! Native terminal I/O operations for Simple language.
//! All operations delegate to the native I/O layer (interpreter_native_io).

use crate::error::CompileError;
use crate::value::Value;
use super::super::interpreter_native_io as native_io;

/// Get stdin handle
///
/// No effect check - returns handle constant
pub fn native_stdin(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_stdin(args)
}

/// Get stdout handle
///
/// No effect check - returns handle constant
pub fn native_stdout(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_stdout(args)
}

/// Get stderr handle
///
/// No effect check - returns handle constant
pub fn native_stderr(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_stderr(args)
}

/// Check if file descriptor is a TTY
///
/// No effect check - query operation
pub fn native_is_tty(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_is_tty(args)
}

/// Enable raw terminal mode
///
/// No effect check - configuration operation
pub fn native_enable_raw_mode(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_enable_raw_mode(args)
}

/// Disable raw terminal mode
///
/// No effect check - configuration operation
pub fn native_disable_raw_mode(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_disable_raw_mode(args)
}

/// Get terminal size (columns, rows)
///
/// No effect check - query operation
pub fn native_get_term_size(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_get_term_size(args)
}

/// Write to terminal
///
/// # Effect
/// * Requires terminal write effect
pub fn native_term_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_write")?;
    native_io::native_term_write(args)
}

/// Read from terminal
///
/// # Effect
/// * Requires terminal read effect
pub fn native_term_read(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_read")?;
    native_io::native_term_read(args)
}

/// Read from terminal with timeout
///
/// # Effect
/// * Requires terminal read effect
pub fn native_term_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_read_timeout")?;
    native_io::native_term_read_timeout(args)
}

/// Flush terminal output
///
/// # Effect
/// * Requires terminal write effect
pub fn native_term_flush(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_flush")?;
    native_io::native_term_flush(args)
}

/// Poll terminal for input availability
///
/// # Effect
/// * Requires terminal read effect
pub fn native_term_poll(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_poll")?;
    native_io::native_term_poll(args)
}

// ---------------------------------------------------------------------------
// `rt_*` name adapters
//
// src/lib/nogc_sync_mut/tui/terminal.spl (and other low-level TUI code)
// declares `extern fn rt_stdin_read_byte`, `rt_terminal_enable_raw_mode`,
// `rt_terminal_disable_raw_mode`, `rt_terminal_is_tty`, and
// `rt_terminal_get_size` directly — these match the SFFI symbol names in
// src/compiler_rust/runtime/src/value/sffi/env_process.rs, used when a
// program JIT/AOT-compiles. When compilation instead falls back to this
// tree-walking interpreter (e.g. an unrelated HIR lowering failure elsewhere
// in the program), extern calls are dispatched by exact name through
// init_dispatch_table() in interpreter_extern/mod.rs — which only had the
// `native_*` names above (a legacy/pre-`rt_`-prefix naming convention), not
// the `rt_terminal_*`/`rt_stdin_read_byte` names. So a program that JIT-fails
// for any reason and directly calls these `rt_` externs previously hit
// "unknown extern function". These adapters close that gap. See
// doc/08_tracking/bug/raw_mode_extern_registry_2026-07-03.md.
// ---------------------------------------------------------------------------

/// `rt_stdin_read_byte` — read one byte from stdin (no args). Returns the
/// byte value (0-255) or -1 at EOF/error.
pub fn rt_stdin_read_byte(_args: &[Value]) -> Result<Value, CompileError> {
    use std::io::Read;
    let mut byte = [0u8; 1];
    match std::io::stdin().read(&mut byte) {
        Ok(1) => Ok(Value::Int(byte[0] as i64)),
        _ => Ok(Value::Int(-1)),
    }
}

/// `rt_terminal_enable_raw_mode` — bridges to `native_enable_raw_mode` on
/// stdin (handle 0), converting its `i64` status code (0 = ok) to the `bool`
/// the `rt_` extern declares.
pub fn rt_terminal_enable_raw_mode(_args: &[Value]) -> Result<Value, CompileError> {
    let result = native_io::native_enable_raw_mode(&[Value::Int(0)])?;
    Ok(Value::Bool(matches!(result, Value::Int(0))))
}

/// `rt_terminal_disable_raw_mode` — bridges to `native_disable_raw_mode` on
/// stdin (handle 0).
pub fn rt_terminal_disable_raw_mode(_args: &[Value]) -> Result<Value, CompileError> {
    let result = native_io::native_disable_raw_mode(&[Value::Int(0)])?;
    Ok(Value::Bool(matches!(result, Value::Int(0))))
}

/// `rt_terminal_is_tty` — query stdin through the interpreter's native
/// terminal adapter (handle 0).
pub fn rt_terminal_is_tty(_args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_is_tty(&[Value::Int(0)])
}

/// `rt_terminal_stdout_is_tty` — query stdout (handle 1), independently of stdin.
pub fn rt_terminal_stdout_is_tty(_args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_is_tty(&[Value::Int(1)])
}

/// `rt_terminal_get_size` — bridges to `native_get_term_size` on stdout
/// (handle 1, matching `fill_terminal_size`'s `STDOUT_FILENO` in
/// env_process.rs). `native_get_term_size` returns `[rows, cols]`; the `rt_`
/// extern (and `terminal_get_size()` in terminal.spl) expects `(cols, rows)`.
pub fn rt_terminal_get_size(_args: &[Value]) -> Result<Value, CompileError> {
    match native_io::native_get_term_size(&[Value::Int(1)])? {
        Value::Array(items) if items.len() == 2 => Ok(Value::Tuple(vec![items[1].clone(), items[0].clone()])),
        _ => Ok(Value::Tuple(vec![Value::Int(80), Value::Int(24)])),
    }
}

/// `rt_atexit_install` — install a process-exit latch, mirroring
/// `rt_atexit_install` in `src/runtime/runtime.c:2732` /
/// `runtime_hosted_signal.c:44`. `src/lib/nogc_sync_mut/tui/terminal.spl:50`
/// declares and calls this (`terminal_install_recovery`, `:78`) but this
/// interpreter bridge never registered it, so any TUI entry that falls back
/// to the tree-walking interpreter died with `unknown extern function:
/// rt_atexit_install`. See
/// doc/08_tracking/bug/caret_tui_mode_dies_rt_atexit_install_unregistered_2026-09-06.md.
///
/// The C runtime's counterpart installs a real `atexit()` handler that a
/// paired `rt_atexit_check()` later polls; `rt_atexit_check` has no caller
/// and no interpreter bridge anywhere in this crate, so there is nothing that
/// would ever read a latch here. Returning success (matching the C
/// implementation's return value once installed) is therefore sufficient —
/// registering a real `atexit` handler nobody polls would be dead code.
pub fn rt_atexit_install(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}

// ---------------------------------------------------------------------------
// Signal latches (`rt_signal_install` / `rt_signal_check`)
//
// `terminal.spl:48-49` declares these alongside `rt_atexit_install` and
// `terminal_install_recovery()` (`:76-80`) calls `rt_signal_install` on the
// line right after `rt_atexit_install` — so bridging `rt_atexit_install`
// alone still leaves the same TUI entry dying one call later with
// `unknown extern function: rt_signal_install`. Mirrors
// `src/runtime/runtime.c:2650,2706-2730` (`_signal_flags` + `rt_signal_install`
// / `rt_signal_check`): a `sigaction`-installed handler sets a flag; the
// check function reads-and-clears it. Real work (not a stub) because caret's
// resize handling (`terminal_resize_pending`) depends on it actually firing.
// ---------------------------------------------------------------------------

const RT_SIGNAL_MAX: usize = 32;
static RT_SIGNAL_FLAGS: [std::sync::atomic::AtomicBool; RT_SIGNAL_MAX] =
    [const { std::sync::atomic::AtomicBool::new(false) }; RT_SIGNAL_MAX];

extern "C" fn rt_signal_handler(signum: libc::c_int) {
    if signum >= 0 && (signum as usize) < RT_SIGNAL_MAX {
        RT_SIGNAL_FLAGS[signum as usize].store(true, std::sync::atomic::Ordering::SeqCst);
    }
}

/// `rt_signal_install(signal_num)` — install the shared handler for
/// `signal_num`, returning `1` on success / `0` on an out-of-range signal or
/// a failed `sigaction`.
pub fn rt_signal_install(args: &[Value]) -> Result<Value, CompileError> {
    let signal_num = args.first().map(|v| v.as_int()).transpose()?.unwrap_or(-1);
    if !(0..RT_SIGNAL_MAX as i64).contains(&signal_num) {
        return Ok(Value::Int(0));
    }
    let ok = unsafe {
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = rt_signal_handler as usize;
        libc::sigemptyset(&mut sa.sa_mask);
        sa.sa_flags = libc::SA_RESTART;
        libc::sigaction(signal_num as libc::c_int, &sa, std::ptr::null_mut()) == 0
    };
    Ok(Value::Int(if ok { 1 } else { 0 }))
}

/// `rt_signal_check(signal_num)` — read-and-clear the latch for
/// `signal_num`, returning `1` if it had fired since the last check, else
/// `0` (including for an out-of-range signal).
pub fn rt_signal_check(args: &[Value]) -> Result<Value, CompileError> {
    let signal_num = args.first().map(|v| v.as_int()).transpose()?.unwrap_or(-1);
    if !(0..RT_SIGNAL_MAX as i64).contains(&signal_num) {
        return Ok(Value::Int(0));
    }
    let fired = RT_SIGNAL_FLAGS[signal_num as usize].swap(false, std::sync::atomic::Ordering::SeqCst);
    Ok(Value::Int(if fired { 1 } else { 0 }))
}
