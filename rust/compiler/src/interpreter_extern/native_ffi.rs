/// Native compilation and execution FFI functions
///
/// Provides bridge from Simple interpreter to LLVM native code generation.

use crate::compile_error::CompileError;
use crate::runtime_value::RuntimeValue;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

/// Compile Simple source to native executable using LLVM backend
///
/// Callable from Simple as: `rt_compile_to_native(source_path, output_path)`
///
/// Returns: (success: bool, error_message: text)
pub fn rt_compile_to_native(args: &[RuntimeValue]) -> Result<RuntimeValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_compile_to_native requires 2 arguments (source_path, output_path)",
        ));
    }

    let source_path = match &args[0] {
        RuntimeValue::String(s) => s.as_str(),
        _ => return Err(CompileError::runtime("source_path must be a string")),
    };

    let output_path = match &args[1] {
        RuntimeValue::String(s) => s.as_str(),
        _ => return Err(CompileError::runtime("output_path must be a string")),
    };

    // Check if source file exists
    if !Path::new(source_path).exists() {
        let error_msg = format!("Source file not found: {}", source_path);
        return Ok(RuntimeValue::tuple(vec![
            RuntimeValue::Bool(false),
            RuntimeValue::String(error_msg.into()),
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
    Ok(RuntimeValue::tuple(vec![
        RuntimeValue::Bool(false),
        RuntimeValue::String(error_msg.into()),
    ]))
}

/// Execute a native binary with arguments and timeout
///
/// Callable from Simple as: `rt_execute_native(binary_path, args, timeout_ms)`
///
/// Returns: (stdout: text, stderr: text, exit_code: i32)
pub fn rt_execute_native(args: &[RuntimeValue]) -> Result<RuntimeValue, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_execute_native requires 3 arguments (binary_path, args, timeout_ms)",
        ));
    }

    let binary_path = match &args[0] {
        RuntimeValue::String(s) => s.as_str(),
        _ => return Err(CompileError::runtime("binary_path must be a string")),
    };

    let cmd_args = match &args[1] {
        RuntimeValue::Array(arr) => {
            let mut args_vec = Vec::new();
            for arg in arr.iter() {
                match arg {
                    RuntimeValue::String(s) => args_vec.push(s.to_string()),
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
        RuntimeValue::I64(ms) => *ms as u64,
        _ => return Err(CompileError::runtime("timeout_ms must be an integer")),
    };

    // Check if binary exists
    if !Path::new(binary_path).exists() {
        return Ok(RuntimeValue::tuple(vec![
            RuntimeValue::String("".into()),
            RuntimeValue::String(format!("Binary not found: {}", binary_path).into()),
            RuntimeValue::I64(127), // Command not found
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
            return Ok(RuntimeValue::tuple(vec![
                RuntimeValue::String("".into()),
                RuntimeValue::String(format!("Execution error: {}", e).into()),
                RuntimeValue::I64(-1),
            ]));
        }
    };

    let duration_ms = start.elapsed().as_millis() as i64;

    // Check if execution exceeded timeout
    if duration_ms > timeout_ms as i64 {
        return Ok(RuntimeValue::tuple(vec![
            RuntimeValue::String("".into()),
            RuntimeValue::String("Execution timed out".into()),
            RuntimeValue::I64(124), // Timeout exit code
        ]));
    }

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let exit_code = output.status.code().unwrap_or(-1) as i64;

    Ok(RuntimeValue::tuple(vec![
        RuntimeValue::String(stdout.into()),
        RuntimeValue::String(stderr.into()),
        RuntimeValue::I64(exit_code),
    ]))
}

/// Delete a file
///
/// Callable from Simple as: `rt_file_delete(path)`
///
/// Returns: bool (true if deleted successfully)
pub fn rt_file_delete(args: &[RuntimeValue]) -> Result<RuntimeValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_file_delete requires 1 argument (path)",
        ));
    }

    let path = match &args[0] {
        RuntimeValue::String(s) => s.as_str(),
        _ => return Err(CompileError::runtime("path must be a string")),
    };

    match std::fs::remove_file(path) {
        Ok(()) => Ok(RuntimeValue::Bool(true)),
        Err(_) => Ok(RuntimeValue::Bool(false)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_to_native_not_implemented() {
        let args = vec![
            RuntimeValue::String("test.spl".into()),
            RuntimeValue::String("test.out".into()),
        ];
        let result = rt_compile_to_native(&args).unwrap();

        match result {
            RuntimeValue::Tuple(values) => {
                assert_eq!(values.len(), 2);
                assert_eq!(values[0], RuntimeValue::Bool(false));
                match &values[1] {
                    RuntimeValue::String(s) => {
                        assert!(s.contains("not yet implemented"));
                    }
                    _ => panic!("Expected error message"),
                }
            }
            _ => panic!("Expected tuple result"),
        }
    }

    #[test]
    fn test_file_delete_nonexistent() {
        let args = vec![RuntimeValue::String("/tmp/nonexistent_file_xyz123".into())];
        let result = rt_file_delete(&args).unwrap();
        assert_eq!(result, RuntimeValue::Bool(false));
    }
}
