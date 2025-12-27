// Extern function calls (part of interpreter module)

// Import the runtime I/O capture functions
use simple_runtime::value::{
    rt_is_stdout_capturing, rt_is_stderr_capturing,
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

// Extern declarations for REPL runner FFI functions (from driver crate)
extern "C" {
    fn simple_repl_runner_init() -> bool;
    fn simple_repl_runner_cleanup();
    fn simple_repl_runner_execute(code_ptr: *const u8, code_len: usize, result_buffer: *mut u8, result_capacity: usize) -> i32;
    fn simple_repl_runner_clear_prelude() -> bool;
    fn simple_repl_runner_get_prelude(buffer: *mut u8, capacity: usize) -> usize;
}

fn call_extern_function(
    name: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let evaluated: Vec<Value> = args
        .iter()
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .collect::<Result<Vec<_>, _>>()?;

    match name {
        // I/O functions - now use runtime capture system
        "print" => {
            check_effect_violations("print")?;
            for (i, val) in evaluated.iter().enumerate() {
                if i > 0 {
                    print_to_stdout(" ");
                }
                print_to_stdout(&val.to_display_string());
            }
            flush_stdout();
            Ok(Value::Nil)
        }
        "println" => {
            check_effect_violations("println")?;
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
        "eprint" => {
            check_effect_violations("eprint")?;
            for (i, val) in evaluated.iter().enumerate() {
                if i > 0 {
                    print_to_stderr(" ");
                }
                print_to_stderr(&val.to_display_string());
            }
            flush_stderr();
            Ok(Value::Nil)
        }
        "eprintln" => {
            check_effect_violations("eprintln")?;
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
        "input" => {
            check_effect_violations("input")?;
            // Print prompt if provided
            if let Some(prompt) = evaluated.first() {
                print_to_stdout(&prompt.to_display_string());
                flush_stdout();
            }
            use std::io::{self, BufRead};
            let stdin = io::stdin();
            let line = stdin.lock().lines().next()
                .transpose()
                .map_err(|e| CompileError::Semantic(format!("input error: {e}")))?
                .unwrap_or_default();
            Ok(Value::Str(line))
        }

        // Math functions
        "abs" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("abs expects 1 argument".into()))?;
            match val {
                Value::Int(i) => Ok(Value::Int(i.abs())),
                _ => Err(CompileError::Semantic("abs expects integer".into())),
            }
        }
        "min" => {
            let a = evaluated.get(0).ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?.as_int()?;
            let b = evaluated.get(1).ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?.as_int()?;
            Ok(Value::Int(a.min(b)))
        }
        "max" => {
            let a = evaluated.get(0).ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?.as_int()?;
            let b = evaluated.get(1).ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?.as_int()?;
            Ok(Value::Int(a.max(b)))
        }
        "sqrt" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("sqrt expects 1 argument".into()))?.as_int()?;
            Ok(Value::Int((val as f64).sqrt() as i64))
        }
        "floor" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("floor expects 1 argument".into()))?.as_int()?;
            Ok(Value::Int(val))
        }
        "ceil" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("ceil expects 1 argument".into()))?.as_int()?;
            Ok(Value::Int(val))
        }
        "pow" => {
            let base = evaluated.get(0).ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?.as_int()?;
            let exp = evaluated.get(1).ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?.as_int()?;
            Ok(Value::Int(base.pow(exp as u32)))
        }

        // Conversion functions
        "to_string" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("to_string expects 1 argument".into()))?;
            Ok(Value::Str(val.to_display_string()))
        }
        "to_int" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("to_int expects 1 argument".into()))?;
            match val {
                Value::Int(i) => Ok(Value::Int(*i)),
                Value::Str(s) => s.parse::<i64>()
                    .map(Value::Int)
                    .map_err(|_| CompileError::Semantic(format!("cannot convert '{}' to int", s))),
                Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
                _ => Err(CompileError::Semantic("to_int expects string, int, or bool".into())),
            }
        }

        // Process control
        "exit" => {
            let code = evaluated.first()
                .map(|v| v.as_int())
                .transpose()?
                .unwrap_or(0) as i32;
            std::process::exit(code);
        }

        // =====================================================================
        // Native Filesystem Operations (simple/std_lib/src/host/async_nogc/io/fs.spl)
        // =====================================================================
        "native_fs_read" => {
            check_effect_violations("native_fs_read")?;
            native_fs_read(&evaluated)
        }
        "native_fs_write" => {
            check_effect_violations("native_fs_write")?;
            native_fs_write(&evaluated)
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
            let s = evaluated.first()
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
            let s = evaluated.first()
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
            // Get command line arguments passed to the Simple interpreter
            // The args are stored in a thread-local during execution
            let args = get_interpreter_args();
            let list: Vec<Value> = args.iter().map(|s| Value::Str(s.clone())).collect();
            Ok(Value::Array(list))
        }
        "sys_exit" => {
            let code = evaluated.first()
                .map(|v| v.as_int())
                .transpose()?
                .unwrap_or(0) as i32;
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
            let terminal = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("ratatui_terminal_cleanup expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe { ratatui_terminal_cleanup(terminal); }
            Ok(Value::Nil)
        }
        "ratatui_terminal_clear" => {
            let terminal = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("ratatui_terminal_clear expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe { ratatui_terminal_clear(terminal); }
            Ok(Value::Nil)
        }
        "ratatui_textbuffer_new" => {
            let handle = unsafe { ratatui_textbuffer_new() };
            Ok(Value::Int(handle as i64))
        }
        "ratatui_textbuffer_insert_char" => {
            let buffer = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_insert_char expects 2 arguments".into()))?
                .as_int()? as u64;
            let code = evaluated.get(1)
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_insert_char expects 2 arguments".into()))?
                .as_int()? as u32;
            unsafe { ratatui_textbuffer_insert_char(buffer, code); }
            Ok(Value::Nil)
        }
        "ratatui_textbuffer_backspace" => {
            let buffer = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_backspace expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe { ratatui_textbuffer_backspace(buffer); }
            Ok(Value::Nil)
        }
        "ratatui_textbuffer_newline" => {
            let buffer = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("ratatui_textbuffer_newline expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe { ratatui_textbuffer_newline(buffer); }
            Ok(Value::Nil)
        }
        "ratatui_object_destroy" => {
            let handle = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("ratatui_object_destroy expects 1 argument".into()))?
                .as_int()? as u64;
            unsafe { ratatui_object_destroy(handle); }
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
            unsafe { simple_repl_runner_cleanup(); }
            Ok(Value::Nil)
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
