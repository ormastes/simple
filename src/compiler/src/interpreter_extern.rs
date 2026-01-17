//! Extern function calls (part of interpreter module)

use crate::effects::check_effect_violations;
use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef};
use std::collections::HashMap;

// Import parent interpreter types
type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Import shared functions from parent module
use super::{evaluate_expr, get_interpreter_args, is_debug_mode};

// Import diagram tracing
use simple_runtime::value::diagram_ffi;

// Import native I/O and networking functions
use super::interpreter_native_io::*;
use super::interpreter_native_net::*;

// Import the runtime I/O capture functions
use simple_runtime::value::{rt_is_stderr_capturing, rt_is_stdout_capturing};

// Import Vulkan FFI functions
#[cfg(feature = "vulkan")]
use simple_runtime::value::gpu_vulkan::{
    rt_vk_buffer_alloc, rt_vk_buffer_download, rt_vk_buffer_free, rt_vk_buffer_upload,
    rt_vk_device_create, rt_vk_device_free, rt_vk_device_sync,
    rt_vk_kernel_compile, rt_vk_kernel_free, rt_vk_kernel_launch, rt_vk_kernel_launch_1d,
};

// TuiEvent struct matches the C ABI struct in ratatui_tui.rs
#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct TuiEvent {
    event_type: u32,
    key_code: u32,
    key_mods: u32,
    char_value: u32,
}

// Extern declarations for Ratatui FFI functions
extern "C" {
    fn ratatui_terminal_new() -> u64;
    fn ratatui_terminal_cleanup(terminal: u64);
    fn ratatui_terminal_clear(terminal: u64);
    fn ratatui_textbuffer_new() -> u64;
    fn ratatui_textbuffer_insert_char(buffer: u64, code: u32);
    fn ratatui_textbuffer_backspace(buffer: u64);
    fn ratatui_textbuffer_newline(buffer: u64);
    fn ratatui_textbuffer_get_text(buffer: u64, buf_ptr: *mut u8, buf_len: usize) -> usize;
    fn ratatui_textbuffer_set_text(buffer: u64, text_ptr: *const u8, text_len: usize);
    fn ratatui_render_textbuffer(terminal: u64, buffer: u64, prompt_ptr: *const u8, prompt_len: usize);
    fn ratatui_read_event_timeout(timeout_ms: u64) -> TuiEvent;
    fn ratatui_object_destroy(handle: u64);
}

// REPL runner FFI functions - defined in driver crate (repl_runner_ffi.rs)
// We use weak linkage to allow the driver to override these stubs at link time.
// When running tests without the driver, these stubs return safe defaults.
#[cfg(not(target_env = "msvc"))]
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn simple_repl_runner_init() -> bool {
    false
}

#[cfg(not(target_env = "msvc"))]
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn simple_repl_runner_cleanup() {}

#[cfg(not(target_env = "msvc"))]
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn simple_repl_runner_execute(
    _code_ptr: *const u8,
    _code_len: usize,
    _result_buffer: *mut u8,
    _result_capacity: usize,
) -> i32 {
    1
}

#[cfg(not(target_env = "msvc"))]
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn simple_repl_runner_clear_prelude() -> bool {
    true
}

#[cfg(not(target_env = "msvc"))]
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn simple_repl_runner_get_prelude(_buffer: *mut u8, _capacity: usize) -> usize {
    0
}

// MSVC doesn't support weak linkage, so we use extern declarations and handle missing symbols at runtime
#[cfg(target_env = "msvc")]
extern "C" {
    fn simple_repl_runner_init() -> bool;
    fn simple_repl_runner_cleanup();
    fn simple_repl_runner_execute(
        code_ptr: *const u8,
        code_len: usize,
        result_buffer: *mut u8,
        result_capacity: usize,
    ) -> i32;
    fn simple_repl_runner_clear_prelude() -> bool;
    fn simple_repl_runner_get_prelude(buffer: *mut u8, capacity: usize) -> usize;
}

pub(crate) fn call_extern_function(
    name: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Diagram tracing for extern function calls
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call(name);
    }

    let evaluated: Vec<Value> = args
        .iter()
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .collect::<Result<Vec<_>, _>>()?;

    match name {
        // I/O functions - now use runtime capture system
        // print now adds newline by default (like Python)
        "print" => {
            check_effect_violations("print")?;
            for (i, val) in evaluated.iter().enumerate() {
                if i > 0 {
                    print_to_stdout(" ");
                }
                print_to_stdout(&val.to_display_string());
            }
            print_to_stdout("\n");
            flush_stdout();
            Ok(Value::Nil)
        }
        // print_raw prints without newline
        "print_raw" => {
            check_effect_violations("print_raw")?;
            for (i, val) in evaluated.iter().enumerate() {
                if i > 0 {
                    print_to_stdout(" ");
                }
                print_to_stdout(&val.to_display_string());
            }
            flush_stdout();
            Ok(Value::Nil)
        }
        // println is deprecated - show error message
        "println" => {
            return Err(CompileError::runtime(
                "'println' is deprecated. Use 'print' instead (it now adds a newline by default, like Python). For no newline, use 'print_raw'."
            ));
        }
        // eprint now adds newline by default
        "eprint" => {
            check_effect_violations("eprint")?;
            for (i, val) in evaluated.iter().enumerate() {
                if i > 0 {
                    print_to_stderr(" ");
                }
                print_to_stderr(&val.to_display_string());
            }
            print_to_stderr("\n");
            flush_stderr();
            Ok(Value::Nil)
        }
        // eprint_raw prints to stderr without newline
        "eprint_raw" => {
            check_effect_violations("eprint_raw")?;
            for (i, val) in evaluated.iter().enumerate() {
                if i > 0 {
                    print_to_stderr(" ");
                }
                print_to_stderr(&val.to_display_string());
            }
            flush_stderr();
            Ok(Value::Nil)
        }
        // eprintln is deprecated - show error message
        "eprintln" => {
            return Err(CompileError::runtime(
                "'eprintln' is deprecated. Use 'eprint' instead (it now adds a newline by default). For no newline, use 'eprint_raw'."
            ));
        }
        // dprint only prints when debug mode is enabled
        "dprint" => {
            if is_debug_mode() {
                check_effect_violations("dprint")?;
                print_to_stdout("[DEBUG] ");
                for (i, val) in evaluated.iter().enumerate() {
                    if i > 0 {
                        print_to_stdout(" ");
                    }
                    print_to_stdout(&val.to_display_string());
                }
                print_to_stdout("\n");
                flush_stdout();
            }
            Ok(Value::Nil)
        }
        "input" => {
            check_effect_violations("input")?;
            // Print prompt if provided
            if let Some(prompt) = evaluated.first() {
                print_to_stdout(&prompt.to_display_string());
                flush_stdout();
            }
            use std::io::{self, BufRead};
            let stdin = io::stdin();
            let line = stdin
                .lock()
                .lines()
                .next()
                .transpose()
                .map_err(|e| CompileError::Semantic(format!("input error: {e}")))?
                .unwrap_or_default();
            Ok(Value::Str(line))
        }

        // Math functions
        "abs" => {
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("abs expects 1 argument".into()))?;
            match val {
                Value::Int(i) => Ok(Value::Int(i.abs())),
                _ => Err(CompileError::Semantic("abs expects integer".into())),
            }
        }
        "min" => {
            let a = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?
                .as_int()?;
            let b = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?
                .as_int()?;
            Ok(Value::Int(a.min(b)))
        }
        "max" => {
            let a = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?
                .as_int()?;
            let b = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?
                .as_int()?;
            Ok(Value::Int(a.max(b)))
        }
        "sqrt" => {
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("sqrt expects 1 argument".into()))?
                .as_int()?;
            Ok(Value::Int((val as f64).sqrt() as i64))
        }
        "floor" => {
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("floor expects 1 argument".into()))?
                .as_int()?;
            Ok(Value::Int(val))
        }
        "ceil" => {
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("ceil expects 1 argument".into()))?
                .as_int()?;
            Ok(Value::Int(val))
        }
        "pow" => {
            let base = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?
                .as_int()?;
            let exp = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?
                .as_int()?;
            Ok(Value::Int(base.pow(exp as u32)))
        }

        // Time functions
        "rt_time_now_seconds" => unsafe {
            let time = simple_runtime::value::rt_time_now_seconds();
            Ok(Value::Float(time))
        },

        // Atomic bool operations
        "rt_atomic_bool_new" => {
            let initial_val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_new expects 1 argument".into()))?;
            let initial = match initial_val {
                Value::Bool(b) => *b,
                _ => {
                    return Err(CompileError::Semantic(
                        "rt_atomic_bool_new expects bool argument".into(),
                    ))
                }
            };
            unsafe {
                let handle = simple_runtime::value::rt_atomic_bool_new(initial);
                Ok(Value::Int(handle))
            }
        }
        "rt_atomic_bool_load" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_load expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                let value = simple_runtime::value::rt_atomic_bool_load(handle);
                Ok(Value::Bool(value))
            }
        }
        "rt_atomic_bool_store" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_store expects 2 arguments".into()))?
                .as_int()?;
            let value_val = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_store expects 2 arguments".into()))?;
            let value = match value_val {
                Value::Bool(b) => *b,
                _ => {
                    return Err(CompileError::Semantic(
                        "rt_atomic_bool_store expects bool argument".into(),
                    ))
                }
            };
            unsafe {
                simple_runtime::value::rt_atomic_bool_store(handle, value);
                Ok(Value::Nil)
            }
        }
        "rt_atomic_bool_swap" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_swap expects 2 arguments".into()))?
                .as_int()?;
            let value_val = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_swap expects 2 arguments".into()))?;
            let value = match value_val {
                Value::Bool(b) => *b,
                _ => {
                    return Err(CompileError::Semantic(
                        "rt_atomic_bool_swap expects bool argument".into(),
                    ))
                }
            };
            unsafe {
                let old = simple_runtime::value::rt_atomic_bool_swap(handle, value);
                Ok(Value::Bool(old))
            }
        }
        "rt_atomic_bool_free" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_free expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                simple_runtime::value::rt_atomic_bool_free(handle);
                Ok(Value::Nil)
            }
        }

        // Atomic int operations
        "rt_atomic_int_new" => {
            let initial = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_new expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                let handle = simple_runtime::value::rt_atomic_int_new(initial);
                Ok(Value::Int(handle))
            }
        }
        "rt_atomic_int_load" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_load expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                let value = simple_runtime::value::rt_atomic_int_load(handle);
                Ok(Value::Int(value))
            }
        }
        "rt_atomic_int_store" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_store expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_store expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                simple_runtime::value::rt_atomic_int_store(handle, value);
                Ok(Value::Nil)
            }
        }
        "rt_atomic_int_swap" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_swap expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_swap expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                let old = simple_runtime::value::rt_atomic_int_swap(handle, value);
                Ok(Value::Int(old))
            }
        }
        "rt_atomic_int_compare_exchange" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_compare_exchange expects 3 arguments".into()))?
                .as_int()?;
            let current = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_compare_exchange expects 3 arguments".into()))?
                .as_int()?;
            let new = evaluated
                .get(2)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_compare_exchange expects 3 arguments".into()))?
                .as_int()?;
            unsafe {
                let success = simple_runtime::value::rt_atomic_int_compare_exchange(handle, current, new);
                Ok(Value::Bool(success))
            }
        }
        "rt_atomic_int_fetch_add" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_add expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_add expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                let old = simple_runtime::value::rt_atomic_int_fetch_add(handle, value);
                Ok(Value::Int(old))
            }
        }
        "rt_atomic_int_fetch_sub" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_sub expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_sub expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                let old = simple_runtime::value::rt_atomic_int_fetch_sub(handle, value);
                Ok(Value::Int(old))
            }
        }
        "rt_atomic_int_fetch_and" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_and expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_and expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                let old = simple_runtime::value::rt_atomic_int_fetch_and(handle, value);
                Ok(Value::Int(old))
            }
        }
        "rt_atomic_int_fetch_or" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_or expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_or expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                let old = simple_runtime::value::rt_atomic_int_fetch_or(handle, value);
                Ok(Value::Int(old))
            }
        }
        "rt_atomic_int_fetch_xor" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_xor expects 2 arguments".into()))?
                .as_int()?;
            let value = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_xor expects 2 arguments".into()))?
                .as_int()?;
            unsafe {
                let old = simple_runtime::value::rt_atomic_int_fetch_xor(handle, value);
                Ok(Value::Int(old))
            }
        }
        "rt_atomic_int_free" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_int_free expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                simple_runtime::value::rt_atomic_int_free(handle);
                Ok(Value::Nil)
            }
        }

        // Atomic flag operations
        "rt_atomic_flag_new" => unsafe {
            let handle = simple_runtime::value::rt_atomic_flag_new();
            Ok(Value::Int(handle))
        },
        "rt_atomic_flag_test_and_set" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_flag_test_and_set expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                let was_set = simple_runtime::value::rt_atomic_flag_test_and_set(handle);
                Ok(Value::Bool(was_set))
            }
        }
        "rt_atomic_flag_clear" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_flag_clear expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                simple_runtime::value::rt_atomic_flag_clear(handle);
                Ok(Value::Nil)
            }
        }
        "rt_atomic_flag_free" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_atomic_flag_free expects 1 argument".into()))?
                .as_int()?;
            unsafe {
                simple_runtime::value::rt_atomic_flag_free(handle);
                Ok(Value::Nil)
            }
        }

        // Conversion functions
        "to_string" => {
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("to_string expects 1 argument".into()))?;
            Ok(Value::Str(val.to_display_string()))
        }
        "to_int" => {
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("to_int expects 1 argument".into()))?;
            match val {
                Value::Int(i) => Ok(Value::Int(*i)),
                Value::Str(s) => s
                    .parse::<i64>()
                    .map(Value::Int)
                    .map_err(|_| CompileError::Semantic(format!("cannot convert '{}' to int", s))),
                Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
                _ => Err(CompileError::Semantic("to_int expects string, int, or bool".into())),
            }
        }

        // Process control
        "exit" => {
            let code = evaluated.first().map(|v| v.as_int()).transpose()?.unwrap_or(0) as i32;
            std::process::exit(code);
        }

        // =====================================================================
        // Native Filesystem Operations (simple/std_lib/src/host/async_nogc/io/fs.spl)
        // =====================================================================
        "native_fs_exists" => native_fs_exists(&evaluated),
        "native_fs_read" => {
            check_effect_violations("native_fs_read")?;
            native_fs_read(&evaluated)
        }
        "native_fs_read_string" => {
            check_effect_violations("native_fs_read_string")?;
            native_fs_read_string(&evaluated)
        }
        "native_fs_write" => {
            check_effect_violations("native_fs_write")?;
            native_fs_write(&evaluated)
        }
        "native_fs_write_string" => {
            check_effect_violations("native_fs_write_string")?;
            native_fs_write_string(&evaluated)
        }
        "native_fs_append" => {
            check_effect_violations("native_fs_append")?;
            native_fs_append(&evaluated)
        }
        "native_fs_create_dir" => {
            check_effect_violations("native_fs_create_dir")?;
            native_fs_create_dir(&evaluated)
        }
        "native_fs_remove_file" => {
            check_effect_violations("native_fs_remove_file")?;
            native_fs_remove_file(&evaluated)
        }
        "native_fs_remove_dir" => {
            check_effect_violations("native_fs_remove_dir")?;
            native_fs_remove_dir(&evaluated)
        }
        "native_fs_rename" => {
            check_effect_violations("native_fs_rename")?;
            native_fs_rename(&evaluated)
        }
        "native_fs_copy" => {
            check_effect_violations("native_fs_copy")?;
            native_fs_copy(&evaluated)
        }
        "native_fs_metadata" => {
            check_effect_violations("native_fs_metadata")?;
            native_fs_metadata(&evaluated)
        }
        "native_fs_read_dir" => {
            check_effect_violations("native_fs_read_dir")?;
            native_fs_read_dir(&evaluated)
        }
        "native_fs_open" => {
            check_effect_violations("native_fs_open")?;
            native_fs_open(&evaluated)
        }
        "native_file_read" => {
            check_effect_violations("native_file_read")?;
            native_file_read(&evaluated)
        }
        "native_file_write" => {
            check_effect_violations("native_file_write")?;
            native_file_write(&evaluated)
        }
        "native_file_flush" => {
            check_effect_violations("native_file_flush")?;
            native_file_flush(&evaluated)
        }
        "native_file_seek" => {
            check_effect_violations("native_file_seek")?;
            native_file_seek(&evaluated)
        }
        "native_file_sync" => {
            check_effect_violations("native_file_sync")?;
            native_file_sync(&evaluated)
        }
        "native_file_close" => {
            check_effect_violations("native_file_close")?;
            native_file_close(&evaluated)
        }

        // =====================================================================
        // Native Terminal Operations (simple/std_lib/src/host/async_nogc/io/term.spl)
        // =====================================================================
        "native_stdin" => native_stdin(&evaluated),
        "native_stdout" => native_stdout(&evaluated),
        "native_stderr" => native_stderr(&evaluated),
        "native_is_tty" => native_is_tty(&evaluated),
        "native_enable_raw_mode" => native_enable_raw_mode(&evaluated),
        "native_disable_raw_mode" => native_disable_raw_mode(&evaluated),
        "native_get_term_size" => native_get_term_size(&evaluated),
        "native_term_write" => {
            check_effect_violations("native_term_write")?;
            native_term_write(&evaluated)
        }
        "native_term_read" => {
            check_effect_violations("native_term_read")?;
            native_term_read(&evaluated)
        }
        "native_term_read_timeout" => {
            check_effect_violations("native_term_read_timeout")?;
            native_term_read_timeout(&evaluated)
        }
        "native_term_flush" => {
            check_effect_violations("native_term_flush")?;
            native_term_flush(&evaluated)
        }
        "native_term_poll" => {
            check_effect_violations("native_term_poll")?;
            native_term_poll(&evaluated)
        }

        // =====================================================================
        // Native TCP Operations (simple/std_lib/src/host/async_nogc_mut/net/tcp.spl)
        // =====================================================================
        "native_tcp_bind" => {
            check_effect_violations("native_tcp_bind")?;
            native_tcp_bind_interp(&evaluated)
        }
        "native_tcp_accept" => {
            check_effect_violations("native_tcp_accept")?;
            native_tcp_accept_interp(&evaluated)
        }
        "native_tcp_connect" => {
            check_effect_violations("native_tcp_connect")?;
            native_tcp_connect_interp(&evaluated)
        }
        "native_tcp_connect_timeout" => {
            check_effect_violations("native_tcp_connect_timeout")?;
            native_tcp_connect_timeout_interp(&evaluated)
        }
        "native_tcp_read" => {
            check_effect_violations("native_tcp_read")?;
            native_tcp_read_interp(&evaluated)
        }
        "native_tcp_write" => {
            check_effect_violations("native_tcp_write")?;
            native_tcp_write_interp(&evaluated)
        }
        "native_tcp_flush" => {
            check_effect_violations("native_tcp_flush")?;
            native_tcp_flush_interp(&evaluated)
        }
        "native_tcp_shutdown" => {
            check_effect_violations("native_tcp_shutdown")?;
            native_tcp_shutdown_interp(&evaluated)
        }
        "native_tcp_close" => {
            check_effect_violations("native_tcp_close")?;
            native_tcp_close_interp(&evaluated)
        }
        "native_tcp_set_nodelay" => native_tcp_set_nodelay_interp(&evaluated),
        "native_tcp_set_keepalive" => Ok(Value::Nil), // Stub for now
        "native_tcp_set_read_timeout" => native_tcp_set_read_timeout_interp(&evaluated),
        "native_tcp_set_write_timeout" => native_tcp_set_write_timeout_interp(&evaluated),
        "native_tcp_get_nodelay" => native_tcp_get_nodelay_interp(&evaluated),
        "native_tcp_peek" => {
            check_effect_violations("native_tcp_peek")?;
            native_tcp_peek_interp(&evaluated)
        }
        "native_tcp_set_backlog" => Ok(Value::Nil), // No-op, backlog set at bind time

        // =====================================================================
        // Native UDP Operations (simple/std_lib/src/host/async_nogc_mut/net/udp.spl)
        // =====================================================================
        "native_udp_bind" => {
            check_effect_violations("native_udp_bind")?;
            native_udp_bind_interp(&evaluated)
        }
        "native_udp_connect" => {
            check_effect_violations("native_udp_connect")?;
            native_udp_connect_interp(&evaluated)
        }
        "native_udp_recv_from" => {
            check_effect_violations("native_udp_recv_from")?;
            native_udp_recv_from_interp(&evaluated)
        }
        "native_udp_recv" => {
            check_effect_violations("native_udp_recv")?;
            native_udp_recv_interp(&evaluated)
        }
        "native_udp_send_to" => {
            check_effect_violations("native_udp_send_to")?;
            native_udp_send_to_interp(&evaluated)
        }
        "native_udp_send" => {
            check_effect_violations("native_udp_send")?;
            native_udp_send_interp(&evaluated)
        }
        "native_udp_peek_from" => {
            check_effect_violations("native_udp_peek_from")?;
            native_udp_peek_from_interp(&evaluated)
        }
        "native_udp_peek" => {
            check_effect_violations("native_udp_peek")?;
            native_udp_peek_interp(&evaluated)
        }
        "native_udp_peer_addr" => native_udp_peer_addr_interp(&evaluated),
        "native_udp_set_broadcast" => native_udp_set_broadcast_interp(&evaluated),
        "native_udp_set_multicast_loop" => native_udp_set_multicast_loop_interp(&evaluated),
        "native_udp_set_multicast_ttl" => native_udp_set_multicast_ttl_interp(&evaluated),
        "native_udp_set_ttl" => native_udp_set_ttl_interp(&evaluated),
        "native_udp_set_read_timeout" => native_udp_set_read_timeout_interp(&evaluated),
        "native_udp_set_write_timeout" => native_udp_set_write_timeout_interp(&evaluated),
        "native_udp_get_broadcast" => native_udp_get_broadcast_interp(&evaluated),
        "native_udp_get_ttl" => native_udp_get_ttl_interp(&evaluated),
        "native_udp_join_multicast_v4" => native_udp_join_multicast_v4_interp(&evaluated),
        "native_udp_leave_multicast_v4" => native_udp_leave_multicast_v4_interp(&evaluated),
        "native_udp_join_multicast_v6" => native_udp_join_multicast_v6_interp(&evaluated),
        "native_udp_leave_multicast_v6" => native_udp_leave_multicast_v6_interp(&evaluated),
        "native_udp_close" => {
            check_effect_violations("native_udp_close")?;
            native_udp_close_interp(&evaluated)
        }

        // =====================================================================
        // Native HTTP Operations (simple/std_lib/src/host/async_nogc_mut/net/http.spl)
        // =====================================================================
        "native_http_send" => {
            check_effect_violations("native_http_send")?;
            native_http_send_interp(&evaluated)
        }

        // =====================================================================
        // MCP Stdio Operations (simple/std_lib/src/mcp/core/transport.spl)
        // =====================================================================
        "stdin_read_char" => {
            check_effect_violations("stdin_read_char")?;
            use std::io::Read;
            let mut buf = [0u8; 1];
            match std::io::stdin().read(&mut buf) {
                Ok(0) => Ok(Value::Str(String::new())), // EOF
                Ok(_) => Ok(Value::Str(String::from_utf8_lossy(&buf).to_string())),
                Err(_) => Ok(Value::Str(String::new())), // Error treated as EOF
            }
        }
        "stdout_write" => {
            check_effect_violations("stdout_write")?;
            let s = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("stdout_write expects 1 argument".into()))?
                .to_display_string();
            print_to_stdout(&s);
            Ok(Value::Nil)
        }
        "stdout_flush" => {
            check_effect_violations("stdout_flush")?;
            flush_stdout();
            Ok(Value::Nil)
        }
        "stderr_write" => {
            check_effect_violations("stderr_write")?;
            let s = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("stderr_write expects 1 argument".into()))?
                .to_display_string();
            print_to_stderr(&s);
            Ok(Value::Nil)
        }
        "stderr_flush" => {
            check_effect_violations("stderr_flush")?;
            flush_stderr();
            Ok(Value::Nil)
        }

        // =====================================================================
        // System Operations (simple/app/mcp/main.spl)
        // =====================================================================
        "sys_get_args" => {
            // Get command line arguments from runtime FFI (unified approach)
            use crate::value_bridge::runtime_to_value;
            use simple_runtime::value::rt_get_args;

            let runtime_array = rt_get_args();
            let value = runtime_to_value(runtime_array);

            Ok(value)
        }
        "sys_exit" => {
            let code = evaluated.first().map(|v| v.as_int()).transpose()?.unwrap_or(0) as i32;
            std::process::exit(code);
        }

        // =====================================================================
        // Ratatui TUI Functions (simple/std_lib/src/ui/tui/backend/ratatui.spl)
        // =====================================================================
        "ratatui_terminal_new" => {
            let handle = unsafe { ratatui_terminal_new() };
            Ok(Value::Int(handle as i64))
        }
        "ratatui_terminal_cleanup" => {
            let terminal = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("ratatui_terminal_cleanup expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe {
                ratatui_terminal_cleanup(terminal);
            }
            Ok(Value::Nil)
        }
        "ratatui_terminal_clear" => {
            let terminal = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("ratatui_terminal_clear expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe {
                ratatui_terminal_clear(terminal);
            }
            Ok(Value::Nil)
        }
        "ratatui_textbuffer_new" => {
            let handle = unsafe { ratatui_textbuffer_new() };
            Ok(Value::Int(handle as i64))
        }
        "ratatui_textbuffer_insert_char" => {
            let buffer = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_insert_char expects 2 arguments".into()))?
                .as_int()? as u64;
            let code = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_insert_char expects 2 arguments".into()))?
                .as_int()? as u32;
            unsafe {
                ratatui_textbuffer_insert_char(buffer, code);
            }
            Ok(Value::Nil)
        }
        "ratatui_textbuffer_backspace" => {
            let buffer = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_backspace expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe {
                ratatui_textbuffer_backspace(buffer);
            }
            Ok(Value::Nil)
        }
        "ratatui_textbuffer_newline" => {
            let buffer = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_newline expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe {
                ratatui_textbuffer_newline(buffer);
            }
            Ok(Value::Nil)
        }
        "ratatui_object_destroy" => {
            let handle = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("ratatui_object_destroy expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe {
                ratatui_object_destroy(handle);
            }
            Ok(Value::Nil)
        }

        // =====================================================================
        // REPL Runner Functions (simple/std_lib/src/repl/__init__.spl)
        // =====================================================================
        "simple_repl_runner_init" => {
            let success = unsafe { simple_repl_runner_init() };
            Ok(Value::Bool(success))
        }
        "simple_repl_runner_cleanup" => {
            unsafe {
                simple_repl_runner_cleanup();
            }
            Ok(Value::Nil)
        }

        // =====================================================================
        // Layout Marker Functions (simple/std_lib/src/layout/markers.spl)
        // Used for profiling and 4KB page locality optimization
        // =====================================================================
        "simple_layout_mark" => {
            // Record layout marker for 4KB page locality optimization.
            // When running with --layout-record, this tracks phase boundaries
            // (startup, first_frame, event_loop) for optimal code placement.
            let val = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("simple_layout_mark expects 1 argument".into()))?;

            let marker_name = match val {
                Value::Str(s) => s.clone(),
                Value::Symbol(s) => s.clone(),
                _ => {
                    return Err(CompileError::Semantic(
                        "simple_layout_mark expects a string argument".into(),
                    ))
                }
            };

            // Record the marker if layout recording is enabled
            crate::layout_recorder::record_layout_marker(&marker_name);

            // In debug builds, log the marker for verification
            #[cfg(debug_assertions)]
            {
                tracing::debug!(marker = %marker_name, "layout marker reached");
            }

            Ok(Value::Nil)
        }

        // =====================================================================
        // Vulkan FFI Functions (simple/std_lib/src/ui/gui/vulkan_ffi.spl)
        // =====================================================================
        #[cfg(feature = "vulkan")]
        "rt_vk_device_create" => {
            let handle = rt_vk_device_create();
            Ok(Value::Int(handle as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_device_free" => {
            let device = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_vk_device_free expects 1 argument".into()))?
                .as_int()? as u64;
            let result = rt_vk_device_free(device);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_device_sync" => {
            let device = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_vk_device_sync expects 1 argument".into()))?
                .as_int()? as u64;
            let result = rt_vk_device_sync(device);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_alloc" => {
            let device = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_alloc expects 2 arguments".into()))?
                .as_int()? as u64;
            let size = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_alloc expects 2 arguments".into()))?
                .as_int()? as u64;
            let handle = rt_vk_buffer_alloc(device, size);
            Ok(Value::Int(handle as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_free" => {
            let buffer = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_free expects 1 argument".into()))?
                .as_int()? as u64;
            let result = rt_vk_buffer_free(buffer);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_upload" => {
            let buffer = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_upload expects 3 arguments".into()))?
                .as_int()? as u64;
            let data_ptr = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_upload expects 3 arguments".into()))?
                .as_ptr()? as *const u8;
            let size = evaluated
                .get(2)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_upload expects 3 arguments".into()))?
                .as_int()? as u64;
            let result = rt_vk_buffer_upload(buffer, data_ptr, size);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_download" => {
            let buffer = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_download expects 3 arguments".into()))?
                .as_int()? as u64;
            let data_ptr = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_download expects 3 arguments".into()))?
                .as_ptr()? as *mut u8;
            let size = evaluated
                .get(2)
                .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_download expects 3 arguments".into()))?
                .as_int()? as u64;
            let result = rt_vk_buffer_download(buffer, data_ptr, size);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_compile" => {
            let device = evaluated
                .get(0)
                .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_compile expects 3 arguments".into()))?
                .as_int()? as u64;
            let spirv_ptr = evaluated
                .get(1)
                .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_compile expects 3 arguments".into()))?
                .as_ptr()? as *const u8;
            let spirv_size = evaluated
                .get(2)
                .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_compile expects 3 arguments".into()))?
                .as_int()? as u64;
            let handle = rt_vk_kernel_compile(device, spirv_ptr, spirv_size);
            Ok(Value::Int(handle as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_free" => {
            let pipeline = evaluated
                .first()
                .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_free expects 1 argument".into()))?
                .as_int()? as u64;
            let result = rt_vk_kernel_free(pipeline);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_launch" => {
            let device = evaluated.get(0).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 6 arguments".into()))?.as_int()? as u64;
            let pipeline = evaluated.get(1).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 6 arguments".into()))?.as_int()? as u64;
            let buffer = evaluated.get(2).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 6 arguments".into()))?.as_int()? as u64;
            let groups_x = evaluated.get(3).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 6 arguments".into()))?.as_int()? as u32;
            let groups_y = evaluated.get(4).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 6 arguments".into()))?.as_int()? as u32;
            let groups_z = evaluated.get(5).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 6 arguments".into()))?.as_int()? as u32;
            let result = rt_vk_kernel_launch(device, pipeline, buffer, groups_x, groups_y, groups_z);
            Ok(Value::Int(result as i64))
        }
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_launch_1d" => {
            let device = evaluated.get(0).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?.as_int()? as u64;
            let pipeline = evaluated.get(1).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?.as_int()? as u64;
            let buffer = evaluated.get(2).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?.as_int()? as u64;
            let num_elements = evaluated.get(3).ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?.as_int()? as u32;
            let result = rt_vk_kernel_launch_1d(device, pipeline, buffer, num_elements);
            Ok(Value::Int(result as i64))
        }

        // Unknown extern function
        _ => Err(CompileError::Semantic(format!("unknown extern function: {}", name))),
    }
}

// Helper functions for I/O that respect capture mode
fn print_to_stdout(s: &str) {
    unsafe {
        simple_runtime::value::rt_print_str(s.as_ptr(), s.len() as u64);
    }
}

fn print_to_stderr(s: &str) {
    unsafe {
        simple_runtime::value::rt_eprint_str(s.as_ptr(), s.len() as u64);
    }
}

fn flush_stdout() {
    use std::io::Write;
    if !rt_is_stdout_capturing() {
        let _ = std::io::stdout().flush();
    }
}

fn flush_stderr() {
    use std::io::Write;
    if !rt_is_stderr_capturing() {
        let _ = std::io::stderr().flush();
    }
}
