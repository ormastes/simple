//! Native JIT extern bridge for tiered compilation.
//!
//! Exposes the full compilation pipeline (parse → HIR → MIR → Cranelift JIT)
//! as interpreter externs. The Simple-side tiered JIT manager calls these at
//! tier promotion time to compile functions to native code.

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

use crate::codegen::execution_manager::ExecutionManager;
use crate::codegen::local_execution::{LocalExecutionManager, JitBackend};
use crate::error::CompileError;
use crate::hir;
use crate::mir::lower_to_mir;
use crate::value::Value;
use simple_parser::Parser;

static JIT_INSTANCES: LazyLock<Mutex<HashMap<i64, LocalExecutionManager>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

static NEXT_HANDLE: LazyLock<Mutex<i64>> = LazyLock::new(|| Mutex::new(1));

pub(crate) fn cleanup_handle(handle: i64) -> i64 {
    JIT_INSTANCES.lock().unwrap().remove(&handle);
    0
}

fn next_handle() -> i64 {
    let mut h = NEXT_HANDLE.lock().unwrap();
    let val = *h;
    *h += 1;
    val
}

#[inline]
fn int_arg(args: &[Value], index: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be an integer"
        ))),
    }
}

#[inline]
fn text_arg<'a>(args: &'a [Value], index: usize, symbol: &str) -> Result<&'a str, CompileError> {
    match args.get(index) {
        Some(Value::Str(value)) => Ok(value.as_str()),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be text"
        ))),
    }
}

fn require_jit_handle(handle: i64, symbol: &str) -> Result<(), CompileError> {
    if JIT_INSTANCES.lock().unwrap().contains_key(&handle) {
        Ok(())
    } else {
        Err(CompileError::runtime(format!("{symbol}: invalid JIT handle {handle}")))
    }
}

/// rt_jit_create() -> i64
/// Creates a new Cranelift JIT instance. Returns handle (>0) or -1 on failure.
pub fn rt_jit_create(_args: &[Value]) -> Result<Value, CompileError> {
    match LocalExecutionManager::new(JitBackend::Cranelift) {
        Ok(em) => {
            let handle = next_handle();
            JIT_INSTANCES.lock().unwrap().insert(handle, em);
            Ok(Value::Int(handle))
        }
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// rt_jit_create_for_target(arch: text) -> i64
/// Creates a JIT instance targeting a specific architecture.
/// arch: "x86_64", "x86_32", "aarch64", "arm32", "riscv64", "riscv32"
/// Routes 32-bit targets through LLVM, 64-bit through Cranelift.
/// Returns handle (>0) or -1 on failure.
pub fn rt_jit_create_for_target(args: &[Value]) -> Result<Value, CompileError> {
    let arch_name = text_arg(args, 0, "rt_jit_create_for_target")?;
    let target = match arch_name_to_target(arch_name) {
        Some(t) => t,
        None => return Ok(Value::Int(-2)),
    };
    match LocalExecutionManager::for_target(target) {
        Ok(em) => {
            let handle = next_handle();
            JIT_INSTANCES.lock().unwrap().insert(handle, em);
            Ok(Value::Int(handle))
        }
        Err(_) => Ok(Value::Int(-1)),
    }
}

fn arch_name_to_target(name: &str) -> Option<simple_common::target::Target> {
    use simple_common::target::{Target, TargetArch};
    let host = Target::host();
    let arch = match name {
        "x86_64" => TargetArch::X86_64,
        "x86_32" | "x86" | "i686" => TargetArch::X86,
        "aarch64" | "arm64" => TargetArch::Aarch64,
        "arm32" | "arm" | "armv7" => TargetArch::Arm,
        "riscv64" | "rv64" => TargetArch::Riscv64,
        "riscv32" | "rv32" => TargetArch::Riscv32,
        "host" => return Some(host),
        _ => return None,
    };
    Some(Target { arch, ..host })
}

/// rt_jit_backend_name(handle: i64) -> text
/// Returns the backend name ("cranelift-jit" or "llvm-jit") for a JIT instance.
pub fn rt_jit_backend_name(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_backend_name")?;
    let instances = JIT_INSTANCES.lock().unwrap();
    match instances.get(&handle) {
        Some(em) => Ok(Value::text(em.backend_name().to_string())),
        None => Err(CompileError::runtime(format!(
            "rt_jit_backend_name: invalid JIT handle {handle}"
        ))),
    }
}

/// rt_jit_compile_source(handle: i64, source: text) -> text
/// Compiles Simple source through full pipeline. Returns "" on success, error on failure.
pub fn rt_jit_compile_source(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_compile_source")?;
    let source = text_arg(args, 1, "rt_jit_compile_source")?;

    let mut parser = Parser::new(source);
    let ast = match parser.parse() {
        Ok(a) => a,
        Err(e) => return Ok(Value::text(format!("parse: {:?}", e))),
    };
    let hir_module = match hir::lower(&ast) {
        Ok(h) => h,
        Err(e) => return Ok(Value::text(format!("hir: {:?}", e))),
    };
    let mir_module = match lower_to_mir(&hir_module) {
        Ok(m) => m,
        Err(e) => return Ok(Value::text(format!("mir: {:?}", e))),
    };

    let mut instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get_mut(&handle) {
        Some(j) => j,
        None => {
            return Err(CompileError::runtime(format!(
                "rt_jit_compile_source: invalid JIT handle {handle}"
            )))
        }
    };
    match em.compile_module(&mir_module) {
        Ok(_) => Ok(Value::text(String::new())),
        Err(e) => Ok(Value::text(format!("codegen: {}", e))),
    }
}

/// rt_jit_call_i64(handle: i64, name: text, arg: i64) -> i64
/// Calls a compiled function with one i64 argument. Returns result or -1 on error.
pub fn rt_jit_call_i64(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_call_i64")?;
    let name = text_arg(args, 1, "rt_jit_call_i64")?;
    let arg0 = int_arg(args, 2, "rt_jit_call_i64")?;

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => {
            return Err(CompileError::runtime(format!(
                "rt_jit_call_i64: invalid JIT handle {handle}"
            )))
        }
    };

    match em.execute(name, &[arg0]) {
        Ok(v) => Ok(Value::Int(v)),
        Err(error) => Err(CompileError::runtime(format!(
            "rt_jit_call_i64: execution failed: {error}"
        ))),
    }
}

/// rt_jit_call_void(handle: i64, name: text) -> i64
/// Calls a compiled function with no arguments. Returns result or -1 on error.
pub fn rt_jit_call_void(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_call_void")?;
    let name = text_arg(args, 1, "rt_jit_call_void")?;

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => {
            return Err(CompileError::runtime(format!(
                "rt_jit_call_void: invalid JIT handle {handle}"
            )))
        }
    };

    match em.execute(name, &[]) {
        Ok(v) => Ok(Value::Int(v)),
        Err(error) => Err(CompileError::runtime(format!(
            "rt_jit_call_void: execution failed: {error}"
        ))),
    }
}

/// rt_jit_call_i64_i64(handle: i64, name: text, arg0: i64, arg1: i64) -> i64
/// Calls a compiled function with two i64 arguments.
pub fn rt_jit_call_i64_i64(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_call_i64_i64")?;
    let name = text_arg(args, 1, "rt_jit_call_i64_i64")?;
    let arg0 = int_arg(args, 2, "rt_jit_call_i64_i64")?;
    let arg1 = int_arg(args, 3, "rt_jit_call_i64_i64")?;

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => {
            return Err(CompileError::runtime(format!(
                "rt_jit_call_i64_i64: invalid JIT handle {handle}"
            )))
        }
    };

    match em.execute(name, &[arg0, arg1]) {
        Ok(v) => Ok(Value::Int(v)),
        Err(error) => Err(CompileError::runtime(format!(
            "rt_jit_call_i64_i64: execution failed: {error}"
        ))),
    }
}

/// rt_jit_has_function(handle: i64, name: text) -> bool
pub fn rt_jit_has_function(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_has_function")?;
    let name = text_arg(args, 1, "rt_jit_has_function")?;

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => {
            return Err(CompileError::runtime(format!(
                "rt_jit_has_function: invalid JIT handle {handle}"
            )))
        }
    };

    Ok(Value::Bool(em.has_function(name)))
}

/// rt_jit_cleanup(handle: i64) -> i64
/// Drops the JIT instance and frees native code memory.
pub fn rt_jit_cleanup(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_jit_cleanup")?;
    require_jit_handle(handle, "rt_jit_cleanup")?;
    Ok(Value::Int(cleanup_handle(handle)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cleanup_handle_drops_hosted_jit_instance() {
        let Value::Int(handle) = rt_jit_create(&[]).expect("create JIT") else {
            panic!("expected JIT handle");
        };
        assert!(handle > 0);
        assert!(JIT_INSTANCES.lock().unwrap().contains_key(&handle));
        assert_eq!(cleanup_handle(handle), 0);
        assert!(!JIT_INSTANCES.lock().unwrap().contains_key(&handle));
    }

    #[test]
    fn jit_bridge_rejects_malformed_arguments_and_invalid_handles() {
        assert!(rt_jit_create_for_target(&[]).is_err());
        assert!(rt_jit_create_for_target(&[Value::Int(0)]).is_err());
        assert!(rt_jit_backend_name(&[Value::Bool(false)]).is_err());
        assert!(rt_jit_backend_name(&[Value::Int(i64::MAX)]).is_err());
        assert!(rt_jit_compile_source(&[Value::Int(1)]).is_err());
        assert!(rt_jit_call_i64(&[Value::Int(1), Value::text("function"), Value::Nil,]).is_err());
        assert!(rt_jit_call_void(&[Value::Int(i64::MAX), Value::text("function")]).is_err());
        assert!(rt_jit_has_function(&[Value::Int(i64::MAX), Value::text("function")]).is_err());
        assert!(rt_jit_cleanup(&[]).is_err());
        assert!(rt_jit_cleanup(&[Value::Int(i64::MAX)]).is_err());
    }
}
