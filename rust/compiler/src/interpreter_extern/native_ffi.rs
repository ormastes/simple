/// Native compilation and execution FFI functions
///
/// Provides bridge from Simple interpreter to LLVM native code generation.

use crate::error::CompileError;
use crate::value::Value as Value;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

/// Compile Simple source to native executable using LLVM backend
///
/// Callable from Simple as: `rt_compile_to_native(source_path, output_path)`
///
/// Returns: (success: bool, error_message: text)
pub fn rt_compile_to_native(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_compile_to_native requires 2 arguments (source_path, output_path)",
        ));
    }

    let source_path = match &args[0] {
        Value::Str(s) => s.as_str(),
        _ => return Err(CompileError::runtime("source_path must be a string")),
    };

    let output_path = match &args[1] {
        Value::Str(s) => s.as_str(),
        _ => return Err(CompileError::runtime("output_path must be a string")),
    };

    // Check if source file exists
    if !Path::new(source_path).exists() {
        let error_msg = format!("Source file not found: {}", source_path);
        return Ok(Value::Tuple(vec![
            Value::Bool(false),
            Value::Str(error_msg.into()),
        ]));
    }

    // For now, return "not implemented" - actual LLVM compilation will be added
    // TODO: Implement actual LLVM backend compilation
    // This would involve:
    // 1. Parse and compile source to MIR
    // 2. Lower MIR to LLVM IR
    // 3. Use LLVM to generate native object file
    // 4. Link to create executable

    let error_msg = "Native compilation not yet implemented - LLVM backend in progress";
    Ok(Value::Tuple(vec![
        Value::Bool(false),
        Value::Str(error_msg.into()),
    ]))
}

/// Execute a native binary with arguments and timeout
///
/// Callable from Simple as: `rt_execute_native(binary_path, args, timeout_ms)`
///
/// Returns: (stdout: text, stderr: text, exit_code: i32)
pub fn rt_execute_native(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_execute_native requires 3 arguments (binary_path, args, timeout_ms)",
        ));
    }

    let binary_path = match &args[0] {
        Value::Str(s) => s.as_str(),
        _ => return Err(CompileError::runtime("binary_path must be a string")),
    };

    let cmd_args = match &args[1] {
        Value::Array(arr) => {
            let mut args_vec = Vec::new();
            for arg in arr.iter() {
                match arg {
                    Value::Str(s) => args_vec.push(s.to_string()),
                    _ => {
                        return Err(CompileError::runtime(
                            "all arguments must be strings",
                        ))
                    }
                }
            }
            args_vec
        }
        _ => return Err(CompileError::runtime("args must be an array")),
    };

    let timeout_ms = match &args[2] {
        Value::Int(ms) => *ms as u64,
        _ => return Err(CompileError::runtime("timeout_ms must be an integer")),
    };

    // Check if binary exists
    if !Path::new(binary_path).exists() {
        return Ok(Value::Tuple(vec![
            Value::Str("".into()),
            Value::Str(format!("Binary not found: {}", binary_path).into()),
            Value::Int(127), // Command not found
        ]));
    }

    // Execute binary with timeout
    let start = Instant::now();
    let output = match Command::new(binary_path)
        .args(&cmd_args)
        .output()
    {
        Ok(output) => output,
        Err(e) => {
            return Ok(Value::Tuple(vec![
                Value::Str("".into()),
                Value::Str(format!("Execution error: {}", e).into()),
                Value::Int(-1),
            ]));
        }
    };

    let duration_ms = start.elapsed().as_millis() as i64;

    // Check if execution exceeded timeout
    if duration_ms > timeout_ms as i64 {
        return Ok(Value::Tuple(vec![
            Value::Str("".into()),
            Value::Str("Execution timed out".into()),
            Value::Int(124), // Timeout exit code
        ]));
    }

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let exit_code = output.status.code().unwrap_or(-1) as i64;

    Ok(Value::Tuple(vec![
        Value::Str(stdout.into()),
        Value::Str(stderr.into()),
        Value::Int(exit_code),
    ]))
}

/// Delete a file
///
/// Callable from Simple as: `rt_file_delete(path)`
///
/// Returns: bool (true if deleted successfully)
pub fn rt_file_delete(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_file_delete requires 1 argument (path)",
        ));
    }

    let path = match &args[0] {
        Value::Str(s) => s.as_str(),
        _ => return Err(CompileError::runtime("path must be a string")),
    };

    match std::fs::remove_file(path) {
        Ok(()) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_to_native_not_implemented() {
        // Create a temp file so we reach the "not yet implemented" path
        let tmp = std::env::temp_dir().join("simple_test_native.spl");
        std::fs::write(&tmp, "fn main(): pass").unwrap();
        let args = vec![
            Value::Str(tmp.to_string_lossy().into()),
            Value::Str("test.out".into()),
        ];
        let result = rt_compile_to_native(&args).unwrap();
        let _ = std::fs::remove_file(&tmp);

        match result {
            Value::Tuple(values) => {
                assert_eq!(values.len(), 2);
                assert_eq!(values[0], Value::Bool(false));
                match &values[1] {
                    Value::Str(s) => {
                        assert!(s.contains("not yet implemented") || s.contains("not implemented") || s.contains("Not"));
                    }
                    _ => panic!("Expected error message"),
                }
            }
            _ => panic!("Expected tuple result"),
        }
    }

    #[test]
    fn test_file_delete_nonexistent() {
        let args = vec![Value::Str("/tmp/nonexistent_file_xyz123".into())];
        let result = rt_file_delete(&args).unwrap();
        assert_eq!(result, Value::Bool(false));
    }
}
