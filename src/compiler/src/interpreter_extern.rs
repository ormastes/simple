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
