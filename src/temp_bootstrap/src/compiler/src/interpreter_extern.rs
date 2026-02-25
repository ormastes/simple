// Extern function calls (part of interpreter module)

// Import the runtime I/O capture functions
use simple_runtime::value::{
    rt_is_stdout_capturing, rt_is_stderr_capturing,
};

fn call_extern_function(
    name: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
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
            check_async_violation("print")?;
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
            check_async_violation("println")?;
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
            check_async_violation("eprint")?;
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
            check_async_violation("eprintln")?;
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
            check_async_violation("input")?;
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

        // Assertion
        "assert" => {
            let condition = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("assert expects at least 1 argument".into()))?;
            if !condition.truthy() {
                let msg = evaluated.get(1)
                    .map(|v| v.to_display_string())
                    .unwrap_or_else(|| "assertion failed".to_string());
                return Err(CompileError::Semantic(format!("assertion failed: {}", msg)));
            }
            Ok(Value::Nil)
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
            check_async_violation("native_fs_read")?;
            native_fs_read(&evaluated)
        }
        "native_fs_write" => {
            check_async_violation("native_fs_write")?;
            native_fs_write(&evaluated)
        }
        "native_fs_append" => {
            check_async_violation("native_fs_append")?;
            native_fs_append(&evaluated)
        }
        "native_fs_create_dir" => {
            check_async_violation("native_fs_create_dir")?;
            native_fs_create_dir(&evaluated)
        }
        "native_fs_remove_file" => {
            check_async_violation("native_fs_remove_file")?;
            native_fs_remove_file(&evaluated)
        }
        "native_fs_remove_dir" => {
            check_async_violation("native_fs_remove_dir")?;
            native_fs_remove_dir(&evaluated)
        }
        "native_fs_rename" => {
            check_async_violation("native_fs_rename")?;
            native_fs_rename(&evaluated)
        }
        "native_fs_copy" => {
            check_async_violation("native_fs_copy")?;
            native_fs_copy(&evaluated)
        }
        "native_fs_metadata" => {
            check_async_violation("native_fs_metadata")?;
            native_fs_metadata(&evaluated)
        }
        "native_fs_read_dir" => {
            check_async_violation("native_fs_read_dir")?;
            native_fs_read_dir(&evaluated)
        }
        "native_fs_open" => {
            check_async_violation("native_fs_open")?;
            native_fs_open(&evaluated)
        }
        "native_file_read" => {
            check_async_violation("native_file_read")?;
            native_file_read(&evaluated)
        }
        "native_file_write" => {
            check_async_violation("native_file_write")?;
            native_file_write(&evaluated)
        }
        "native_file_flush" => {
            check_async_violation("native_file_flush")?;
            native_file_flush(&evaluated)
        }
        "native_file_seek" => {
            check_async_violation("native_file_seek")?;
            native_file_seek(&evaluated)
        }
        "native_file_sync" => {
            check_async_violation("native_file_sync")?;
            native_file_sync(&evaluated)
        }
        "native_file_close" => {
            check_async_violation("native_file_close")?;
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
            check_async_violation("native_term_write")?;
            native_term_write(&evaluated)
        }
        "native_term_read" => {
            check_async_violation("native_term_read")?;
            native_term_read(&evaluated)
        }
        "native_term_read_timeout" => {
            check_async_violation("native_term_read_timeout")?;
            native_term_read_timeout(&evaluated)
        }
        "native_term_flush" => {
            check_async_violation("native_term_flush")?;
            native_term_flush(&evaluated)
        }
        "native_term_poll" => {
            check_async_violation("native_term_poll")?;
            native_term_poll(&evaluated)
        }

        // =====================================================================
        // Runtime FFI stubs (rt_* functions used by compiler source)
        // =====================================================================
        "file_exists" | "rt_file_exists" => {
            check_async_violation("file_exists")?;
            let path = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("file_exists expects 1 argument".into()))?
                .to_display_string();
            Ok(Value::Bool(std::path::Path::new(&path).exists()))
        }
        "get_host_os" | "rt_get_host_os" => {
            let os = if cfg!(target_os = "linux") {
                "linux"
            } else if cfg!(target_os = "macos") {
                "macos"
            } else if cfg!(target_os = "windows") {
                "windows"
            } else {
                "unknown"
            };
            Ok(Value::Str(os.to_string()))
        }
        "shell" | "rt_shell" | "rt_exec" => {
            check_async_violation("shell")?;
            let cmd = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("shell expects 1 argument".into()))?
                .to_display_string();
            let output = std::process::Command::new("sh")
                .arg("-c")
                .arg(&cmd)
                .output()
                .map_err(|e| CompileError::Semantic(format!("shell error: {}", e)))?;
            Ok(Value::Str(String::from_utf8_lossy(&output.stdout).to_string()))
        }
        "rt_hash_text" => {
            let s = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_hash_text expects 1 argument".into()))?
                .to_display_string();
            // Simple hash function (djb2)
            let mut hash: i64 = 5381;
            for byte in s.bytes() {
                hash = hash.wrapping_mul(33).wrapping_add(byte as i64);
            }
            Ok(Value::Int(hash))
        }
        "io_file_write" | "rt_file_write" | "rt_file_write_text" => {
            check_async_violation("io_file_write")?;
            let path = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("io_file_write expects 2 arguments".into()))?
                .to_display_string();
            let content = evaluated.get(1)
                .ok_or_else(|| CompileError::Semantic("io_file_write expects 2 arguments".into()))?
                .to_display_string();
            std::fs::write(&path, &content)
                .map_err(|e| CompileError::Semantic(format!("io_file_write error: {}", e)))?;
            Ok(Value::Nil)
        }
        "io_file_read" | "rt_file_read" | "rt_file_read_text" => {
            check_async_violation("io_file_read")?;
            let path = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("io_file_read expects 1 argument".into()))?
                .to_display_string();
            let content = std::fs::read_to_string(&path)
                .map_err(|e| CompileError::Semantic(format!("io_file_read error: {}", e)))?;
            Ok(Value::Str(content))
        }
        "io_file_append" | "rt_file_append" => {
            check_async_violation("io_file_append")?;
            let path = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("io_file_append expects 2 arguments".into()))?
                .to_display_string();
            let content = evaluated.get(1)
                .ok_or_else(|| CompileError::Semantic("io_file_append expects 2 arguments".into()))?
                .to_display_string();
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(&path)
                .map_err(|e| CompileError::Semantic(format!("io_file_append error: {}", e)))?;
            file.write_all(content.as_bytes())
                .map_err(|e| CompileError::Semantic(format!("io_file_append error: {}", e)))?;
            Ok(Value::Nil)
        }
        "rt_get_env" | "get_env" | "env_get" => {
            let key = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("get_env expects 1 argument".into()))?
                .to_display_string();
            match std::env::var(&key) {
                Ok(val) => Ok(Value::some(Value::Str(val))),
                Err(_) => Ok(Value::none()),
            }
        }
        "rt_get_args" | "sys_get_args" | "get_args" => {
            // If program args were forwarded via -- separator, use those
            // Uses ASCII Unit Separator (0x1F) as delimiter
            if let Ok(forwarded) = std::env::var("SIMPLE_PROGRAM_ARGS") {
                let args: Vec<Value> = forwarded
                    .split('\x1F')
                    .filter(|s| !s.is_empty())
                    .map(|a| Value::Str(a.to_string()))
                    .collect();
                Ok(Value::Array(args))
            } else {
                let args: Vec<Value> = std::env::args().map(|a| Value::Str(a)).collect();
                Ok(Value::Array(args))
            }
        }
        "rt_time_now" | "time_now" => {
            use std::time::{SystemTime, UNIX_EPOCH};
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as i64;
            Ok(Value::Int(now))
        }
        "rt_sleep" | "sleep" => {
            check_async_violation("sleep")?;
            let ms = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("sleep expects 1 argument".into()))?
                .as_int()?;
            std::thread::sleep(std::time::Duration::from_millis(ms as u64));
            Ok(Value::Nil)
        }
        "rt_panic" | "panic" => {
            let msg = evaluated.first()
                .map(|v| v.to_display_string())
                .unwrap_or_else(|| "panic".to_string());
            Err(CompileError::Semantic(format!("panic: {}", msg)))
        }
        "type_of" | "rt_type_of" => {
            let val = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("type_of expects 1 argument".into()))?;
            Ok(Value::Str(val.type_name().to_string()))
        }
        "error" => {
            let msg = evaluated.first()
                .map(|v| v.to_display_string())
                .unwrap_or_else(|| "error".to_string());
            Ok(Value::err(Value::Str(msg)))
        }
        "debug" => {
            let val = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("debug expects 1 argument".into()))?;
            eprintln!("[debug] {:?}", val);
            Ok(Value::Nil)
        }
        "typeof" => {
            let val = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("typeof expects 1 argument".into()))?;
            Ok(Value::Str(val.type_name().to_string()))
        }

        // =====================================================================
        // Path operations
        // =====================================================================
        "rt_path_join" => {
            let a = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("rt_path_join expects 2 arguments".into()))?
                .to_display_string();
            let b = evaluated.get(1)
                .ok_or_else(|| CompileError::Semantic("rt_path_join expects 2 arguments".into()))?
                .to_display_string();
            let joined = std::path::Path::new(&a).join(&b).to_string_lossy().to_string();
            Ok(Value::Str(joined))
        }
        "rt_path_parent" => {
            let p = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_path_parent expects 1 argument".into()))?
                .to_display_string();
            match std::path::Path::new(&p).parent() {
                Some(parent) => Ok(Value::some(Value::Str(parent.to_string_lossy().to_string()))),
                None => Ok(Value::none()),
            }
        }
        "rt_path_exists" => {
            let p = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_path_exists expects 1 argument".into()))?
                .to_display_string();
            Ok(Value::Bool(std::path::Path::new(&p).exists()))
        }
        "rt_dir_exists" => {
            let p = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_dir_exists expects 1 argument".into()))?
                .to_display_string();
            Ok(Value::Bool(std::path::Path::new(&p).is_dir()))
        }

        // =====================================================================
        // Directory operations
        // =====================================================================
        "rt_dir_list" => {
            check_async_violation("rt_dir_list")?;
            let p = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_dir_list expects 1 argument".into()))?
                .to_display_string();
            match std::fs::read_dir(&p) {
                Ok(entries) => {
                    let mut items = Vec::new();
                    for entry in entries {
                        if let Ok(e) = entry {
                            items.push(Value::Str(e.file_name().to_string_lossy().to_string()));
                        }
                    }
                    Ok(Value::Array(items))
                }
                Err(_) => Ok(Value::Array(vec![])),
            }
        }
        "rt_dir_create" => {
            check_async_violation("rt_dir_create")?;
            let p = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_dir_create expects 1 argument".into()))?
                .to_display_string();
            let _ = std::fs::create_dir_all(&p);
            Ok(Value::Nil)
        }

        // =====================================================================
        // File read/write (bytes)
        // =====================================================================
        "rt_file_write_bytes" => {
            check_async_violation("rt_file_write_bytes")?;
            let path = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("rt_file_write_bytes expects 2 arguments".into()))?
                .to_display_string();
            let data = match evaluated.get(1) {
                Some(Value::Array(arr)) => {
                    arr.iter().map(|v| {
                        match v {
                            Value::Int(i) => *i as u8,
                            _ => 0u8,
                        }
                    }).collect::<Vec<u8>>()
                }
                _ => return Err(CompileError::Semantic("rt_file_write_bytes expects byte array".into())),
            };
            let _ = std::fs::write(&path, &data);
            Ok(Value::Nil)
        }
        "rt_file_read_bytes" => {
            check_async_violation("rt_file_read_bytes")?;
            let path = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_file_read_bytes expects 1 argument".into()))?
                .to_display_string();
            match std::fs::read(&path) {
                Ok(bytes) => {
                    let arr = bytes.into_iter().map(|b| Value::Int(b as i64)).collect();
                    Ok(Value::Array(arr))
                }
                Err(_) => Ok(Value::Array(vec![])),
            }
        }

        // =====================================================================
        // Process execution
        // =====================================================================
        "rt_process_run" => {
            check_async_violation("rt_process_run")?;
            let cmd = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("rt_process_run expects 2 arguments".into()))?
                .to_display_string();
            let args_array = match evaluated.get(1) {
                Some(Value::Array(arr)) => arr.iter().map(|v| v.to_display_string()).collect::<Vec<_>>(),
                _ => vec![],
            };
            match std::process::Command::new(&cmd).args(&args_array).output() {
                Ok(output) => {
                    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
                    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
                    let exit_code = output.status.code().unwrap_or(-1) as i64;
                    Ok(Value::Tuple(vec![
                        Value::Str(stdout),
                        Value::Str(stderr),
                        Value::Int(exit_code),
                    ]))
                }
                Err(e) => {
                    Ok(Value::Tuple(vec![
                        Value::Str(String::new()),
                        Value::Str(format!("process error: {}", e)),
                        Value::Int(-1),
                    ]))
                }
            }
        }

        // =====================================================================
        // System information
        // =====================================================================
        "rt_cpu_count" => {
            let count = std::thread::available_parallelism()
                .map(|n| n.get() as i64)
                .unwrap_or(1);
            Ok(Value::Int(count))
        }

        // =====================================================================
        // Time functions (micros and millis)
        // =====================================================================
        "rt_time_now_unix_micros" => {
            use std::time::{SystemTime, UNIX_EPOCH};
            let micros = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_micros() as i64;
            Ok(Value::Int(micros))
        }
        "rt_time_now_unix_ms" => {
            use std::time::{SystemTime, UNIX_EPOCH};
            let ms = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as i64;
            Ok(Value::Int(ms))
        }

        // =====================================================================
        // GC stubs (no-op in bootstrap mode)
        // =====================================================================
        "rt_gc_init" => Ok(Value::Nil),
        "rt_gc_malloc" => Ok(Value::Int(0)),
        "rt_gc_collect" => Ok(Value::Nil),

        // =====================================================================
        // Environment variables
        // =====================================================================
        "rt_env_get" => {
            let key = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_env_get expects 1 argument".into()))?
                .to_display_string();
            match std::env::var(&key) {
                Ok(val) => Ok(Value::some(Value::Str(val))),
                Err(_) => Ok(Value::none()),
            }
        }
        "rt_env_set" => {
            let key = evaluated.get(0)
                .ok_or_else(|| CompileError::Semantic("rt_env_set expects 2 arguments".into()))?
                .to_display_string();
            let val = evaluated.get(1)
                .ok_or_else(|| CompileError::Semantic("rt_env_set expects 2 arguments".into()))?
                .to_display_string();
            // Safety: this is single-threaded bootstrap mode
            unsafe { std::env::set_var(&key, &val); }
            Ok(Value::Nil)
        }

        // =====================================================================
        // String/bytes conversion
        // =====================================================================
        "rt_string_to_bytes" => {
            let s = evaluated.first()
                .ok_or_else(|| CompileError::Semantic("rt_string_to_bytes expects 1 argument".into()))?
                .to_display_string();
            let arr = s.bytes().map(|b| Value::Int(b as i64)).collect();
            Ok(Value::Array(arr))
        }
        "rt_bytes_to_string" => {
            let bytes = match evaluated.first() {
                Some(Value::Array(arr)) => {
                    arr.iter().map(|v| {
                        match v {
                            Value::Int(i) => *i as u8,
                            _ => 0u8,
                        }
                    }).collect::<Vec<u8>>()
                }
                _ => return Err(CompileError::Semantic("rt_bytes_to_string expects byte array".into())),
            };
            Ok(Value::Str(String::from_utf8_lossy(&bytes).to_string()))
        }

        // =====================================================================
        // Catch-all for unknown extern functions — return Nil in bootstrap mode
        // instead of hard errors, to allow files to compile even when their
        // extern fn declarations reference runtime functions we haven't stubbed.
        // =====================================================================
        _ => {
            // In bootstrap mode, unknown extern functions return Nil
            // This allows files to compile even when extern fns are missing
            Ok(Value::Nil)
        }
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
