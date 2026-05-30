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

fn next_handle() -> i64 {
    let mut h = NEXT_HANDLE.lock().unwrap();
    let val = *h;
    *h += 1;
    val
}

fn value_to_i64(val: &Value) -> i64 {
    match val {
        Value::Int(i) => *i,
        _ => 0,
    }
}

fn value_to_str(val: &Value) -> String {
    match val {
        Value::Str(s) => s.clone(),
        _ => String::new(),
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
    if args.is_empty() {
        return Ok(Value::Int(-1));
    }
    let arch_name = value_to_str(&args[0]);
    let target = match arch_name_to_target(&arch_name) {
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
    if args.is_empty() {
        return Ok(Value::Str("invalid".into()));
    }
    let handle = value_to_i64(&args[0]);
    let instances = JIT_INSTANCES.lock().unwrap();
    match instances.get(&handle) {
        Some(em) => Ok(Value::Str(em.backend_name().to_string())),
        None => Ok(Value::Str("invalid".into())),
    }
}

/// rt_jit_compile_source(handle: i64, source: text) -> text
/// Compiles Simple source through full pipeline. Returns "" on success, error on failure.
pub fn rt_jit_compile_source(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Str("missing arguments".into()));
    }
    let handle = value_to_i64(&args[0]);
    let source = value_to_str(&args[1]);

    let mut parser = Parser::new(&source);
    let ast = match parser.parse() {
        Ok(a) => a,
        Err(e) => return Ok(Value::Str(format!("parse: {:?}", e))),
    };
    let hir_module = match hir::lower(&ast) {
        Ok(h) => h,
        Err(e) => return Ok(Value::Str(format!("hir: {:?}", e))),
    };
    let mir_module = match lower_to_mir(&hir_module) {
        Ok(m) => m,
        Err(e) => return Ok(Value::Str(format!("mir: {:?}", e))),
    };

    let mut instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get_mut(&handle) {
        Some(j) => j,
        None => return Ok(Value::Str("invalid handle".into())),
    };
    match em.compile_module(&mir_module) {
        Ok(_) => Ok(Value::Str(String::new())),
        Err(e) => Ok(Value::Str(format!("codegen: {}", e))),
    }
}

/// rt_jit_call_i64(handle: i64, name: text, arg: i64) -> i64
/// Calls a compiled function with one i64 argument. Returns result or -1 on error.
pub fn rt_jit_call_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(-1));
    }
    let handle = value_to_i64(&args[0]);
    let name = value_to_str(&args[1]);
    let arg0 = value_to_i64(&args[2]);

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => return Ok(Value::Int(-1)),
    };

    match em.execute(&name, &[arg0]) {
        Ok(v) => Ok(Value::Int(v)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// rt_jit_call_void(handle: i64, name: text) -> i64
/// Calls a compiled function with no arguments. Returns result or -1 on error.
pub fn rt_jit_call_void(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Int(-1));
    }
    let handle = value_to_i64(&args[0]);
    let name = value_to_str(&args[1]);

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => return Ok(Value::Int(-1)),
    };

    match em.execute(&name, &[]) {
        Ok(v) => Ok(Value::Int(v)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// rt_jit_call_i64_i64(handle: i64, name: text, arg0: i64, arg1: i64) -> i64
/// Calls a compiled function with two i64 arguments.
pub fn rt_jit_call_i64_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Int(-1));
    }
    let handle = value_to_i64(&args[0]);
    let name = value_to_str(&args[1]);
    let arg0 = value_to_i64(&args[2]);
    let arg1 = value_to_i64(&args[3]);

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => return Ok(Value::Int(-1)),
    };

    match em.execute(&name, &[arg0, arg1]) {
        Ok(v) => Ok(Value::Int(v)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// rt_jit_has_function(handle: i64, name: text) -> bool
pub fn rt_jit_has_function(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Bool(false));
    }
    let handle = value_to_i64(&args[0]);
    let name = value_to_str(&args[1]);

    let instances = JIT_INSTANCES.lock().unwrap();
    let em = match instances.get(&handle) {
        Some(j) => j,
        None => return Ok(Value::Bool(false)),
    };

    Ok(Value::Bool(em.has_function(&name)))
}

/// rt_jit_cleanup(handle: i64) -> i64
/// Drops the JIT instance and frees native code memory.
pub fn rt_jit_cleanup(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Int(-1));
    }
    let handle = value_to_i64(&args[0]);
    JIT_INSTANCES.lock().unwrap().remove(&handle);
    Ok(Value::Int(0))
}
