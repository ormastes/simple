#!/usr/bin/env simple
# JIT/Execution Manager SFFI Implementation Guide

**Date:** 2026-02-08
**Status:** Specification Complete - Awaiting Runtime Implementation
**Integration:** Shares code with `src/app/compile/` and loader infrastructure

---

## Overview

This guide shows how to implement the JIT/Execution Manager SFFI wrapper **by reusing existing compiler and loader infrastructure**. The JIT wrapper is a thin orchestration layer that coordinates existing components.

**Key Principle:** Don't duplicate code - share the compiler pipeline!

---

## Architecture: Code Sharing

```
┌─────────────────────────────────────────────────────────────┐
│                    Simple Source Code                        │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ├─ Ahead-of-Time (AOT) Compilation
                       │  ├─ src/app/compile/main.spl
                       │  └─ Produces: Binary or SMF file
                       │
                       └─ Just-in-Time (JIT) Compilation
                          ├─ src/app/io/jit_ffi.spl (THIS)
                          └─ Produces: In-memory executable code

         ┌────────────────────────────────────────┐
         │      SHARED COMPILER PIPELINE          │
         ├────────────────────────────────────────┤
         │  1. Parser (src/app/parser/)           │
         │     Simple source → AST                │
         │                                        │
         │  2. HIR Gen (src/app/hir/)             │
         │     AST → High-level IR                │
         │                                        │
         │  3. MIR Gen (src/app/mir/)             │
         │     HIR → Mid-level IR                 │
         │                                        │
         │  4. Backend                            │
         │     ├─ Cranelift (JIT + AOT)           │
         │     └─ LLVM (AOT only, slower JIT)     │
         └────────────────────────────────────────┘
                       │
                       ├─ AOT: Write to disk (.o, .elf)
                       └─ JIT: Load into memory (execute immediately)
```

**Benefits of Code Sharing:**
1. **Consistency:** JIT and AOT produce identical behavior
2. **Maintenance:** Fix bugs once, both modes benefit
3. **Code Size:** ~300 lines instead of ~2000 lines
4. **Reliability:** Reuse battle-tested compiler code

---

## Integration Points

### 1. Parser Integration

**Location:** `src/app/parser/`

**JIT Wrapper Calls:**
```rust
// In rt_exec_manager_compile_source()
use simple_parser::{Lexer, Parser};

fn compile_source(source: &str) -> Result<AST, String> {
    // Reuse existing parser (same code as AOT compilation)
    let lexer = Lexer::new(source);
    let parser = Parser::new(lexer);
    parser.parse_module()
}
```

**No Code Duplication:** Use existing `Lexer` and `Parser` classes.

---

### 2. Compiler Pipeline Integration

**Location:** `src/app/compile/`, `src/app/hir/`, `src/app/mir/`

**JIT Wrapper Calls:**
```rust
use simple_compiler::{CompilerDriver, CompileOptions};

fn jit_compile(source: &str, opt_level: u8) -> Result<MIR, String> {
    // Reuse existing compiler driver
    let options = CompileOptions {
        opt_level,
        target: "host".to_string(),
        emit: EmitKind::MIR,  // MIR for JIT
    };

    let driver = CompilerDriver::new(options);
    driver.compile_source(source)  // Returns MIR
}
```

**Shared Code:**
- AST → HIR lowering
- HIR → MIR lowering
- Type checking
- Optimization passes

---

### 3. Cranelift JIT Integration

**Crate:** `cranelift-jit = "0.98"`
**Location:** New module `src/runtime/jit/cranelift_backend.rs`

**Implementation:**
```rust
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_codegen::settings;

pub struct CraneliftExecManager {
    module: JITModule,
    context: codegen::Context,
}

impl CraneliftExecManager {
    pub fn new(opt_level: u8) -> Result<Self, String> {
        let mut flag_builder = settings::builder();

        // Set optimization level
        match opt_level {
            0 => flag_builder.set("opt_level", "none").unwrap(),
            1 => flag_builder.set("opt_level", "speed").unwrap(),
            2 => flag_builder.set("opt_level", "speed").unwrap(),
            3 => flag_builder.set("opt_level", "speed_and_size").unwrap(),
            _ => return Err("Invalid opt level".to_string()),
        }

        let isa_builder = cranelift_native::builder()
            .map_err(|e| format!("ISA error: {}", e))?;

        let isa = isa_builder.finish(settings::Flags::new(flag_builder))
            .map_err(|e| format!("ISA build error: {}", e))?;

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        let module = JITModule::new(builder);

        Ok(Self {
            module,
            context: codegen::Context::new(),
        })
    }

    pub fn compile_mir(&mut self, mir: &MIR) -> Result<(), String> {
        // REUSE EXISTING MIR → Cranelift translation
        // (Already implemented in src/app/backend/cranelift/)

        use simple_backend::cranelift::MirToCranelift;

        let translator = MirToCranelift::new(&mut self.module, &mut self.context);
        translator.translate_module(mir)
    }

    pub fn get_function_ptr(&mut self, name: &str) -> Result<*const u8, String> {
        let func_id = self.module.get_name(name)
            .ok_or_else(|| format!("Function '{}' not found", name))?;

        self.module.finalize_definitions()
            .map_err(|e| format!("Finalize error: {}", e))?;

        let code_ptr = self.module.get_finalized_function(func_id);
        Ok(code_ptr)
    }

    pub fn execute(&mut self, name: &str, args: &[i64]) -> Result<i64, String> {
        let func_ptr = self.get_function_ptr(name)?;

        // Cast to function type and call
        unsafe {
            match args.len() {
                0 => {
                    let func: fn() -> i64 = std::mem::transmute(func_ptr);
                    Ok(func())
                }
                1 => {
                    let func: fn(i64) -> i64 = std::mem::transmute(func_ptr);
                    Ok(func(args[0]))
                }
                2 => {
                    let func: fn(i64, i64) -> i64 = std::mem::transmute(func_ptr);
                    Ok(func(args[0], args[1]))
                }
                _ => Err("Too many args (max 2 supported)".to_string()),
            }
        }
    }
}
```

**Key Point:** Reuse `MirToCranelift` translator from existing backend!

---

### 4. LLVM JIT Integration (Optional)

**Crate:** `inkwell = "0.2"` (LLVM bindings)
**Location:** New module `src/runtime/jit/llvm_backend.rs`

**Implementation:**
```rust
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::OptimizationLevel;

pub struct LLVMExecManager<'ctx> {
    context: &'ctx Context,
    execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> LLVMExecManager<'ctx> {
    pub fn new(context: &'ctx Context, opt_level: u8) -> Result<Self, String> {
        let opt = match opt_level {
            0 => OptimizationLevel::None,
            1 => OptimizationLevel::Less,
            2 => OptimizationLevel::Default,
            3 => OptimizationLevel::Aggressive,
            _ => OptimizationLevel::Default,
        };

        // Create module and execution engine
        let module = context.create_module("jit");
        let execution_engine = module.create_jit_execution_engine(opt)
            .map_err(|e| format!("LLVM JIT error: {}", e))?;

        Ok(Self {
            context,
            execution_engine,
        })
    }

    pub fn compile_mir(&mut self, mir: &MIR) -> Result<(), String> {
        // REUSE EXISTING MIR → LLVM translation
        // (Already implemented in src/app/backend/llvm_backend.spl!)

        use simple_backend::llvm::MirToLlvm;

        let translator = MirToLlvm::new(self.context);
        translator.translate_module(mir)?;

        Ok(())
    }

    pub fn execute(&self, name: &str, args: &[i64]) -> Result<i64, String> {
        unsafe {
            let func: JitFunction<unsafe extern "C" fn(i64, i64) -> i64> =
                self.execution_engine.get_function(name)
                    .map_err(|e| format!("Function '{}' not found: {}", name, e))?;

            Ok(func.call(args[0], args[1]))
        }
    }
}
```

**Key Point:** Reuse `MirToLlvm` translator from existing LLVM backend!

---

## Complete Runtime Implementation

### File Structure

```
src/runtime/jit/
├── mod.rs                   # Main JIT module
├── handles.rs               # Handle management (same pattern as other wrappers)
├── cranelift_backend.rs     # Cranelift JIT implementation
├── llvm_backend.rs          # LLVM JIT implementation (optional)
└── ffi.rs                   # FFI exports for Simple

Total: ~800-1000 lines Rust (mostly FFI glue)
```

### Main Module (`mod.rs`)

```rust
// src/runtime/jit/mod.rs

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

pub mod handles;
pub mod cranelift_backend;
pub mod ffi;

#[cfg(feature = "llvm-jit")]
pub mod llvm_backend;

use simple_compiler::MIR;

pub enum Backend {
    Auto,
    Cranelift,
    #[cfg(feature = "llvm-jit")]
    LLVM,
}

pub struct ExecManager {
    backend: Backend,
    cranelift: Option<cranelift_backend::CraneliftExecManager>,
    #[cfg(feature = "llvm-jit")]
    llvm: Option<llvm_backend::LLVMExecManager<'static>>,
    opt_level: u8,
    last_error: String,
}

impl ExecManager {
    pub fn new(backend: Backend, opt_level: u8) -> Result<Self, String> {
        let backend = match backend {
            Backend::Auto => {
                // Prefer Cranelift (fast compile)
                Backend::Cranelift
            }
            other => other,
        };

        let mut manager = Self {
            backend,
            cranelift: None,
            #[cfg(feature = "llvm-jit")]
            llvm: None,
            opt_level,
            last_error: String::new(),
        };

        // Initialize selected backend
        match manager.backend {
            Backend::Cranelift => {
                manager.cranelift = Some(cranelift_backend::CraneliftExecManager::new(opt_level)?);
            }
            #[cfg(feature = "llvm-jit")]
            Backend::LLVM => {
                manager.llvm = Some(llvm_backend::LLVMExecManager::new(opt_level)?);
            }
            _ => return Err("Backend not available".to_string()),
        }

        Ok(manager)
    }

    pub fn compile_source(&mut self, source: &str) -> Result<(), String> {
        // INTEGRATION POINT: Use existing compiler pipeline
        use simple_compiler::CompilerDriver;

        let driver = CompilerDriver::new_for_jit(self.opt_level);
        let mir = driver.compile_source(source)?;

        self.compile_mir(&mir)
    }

    pub fn compile_mir(&mut self, mir: &MIR) -> Result<(), String> {
        match &mut self.cranelift {
            Some(backend) => backend.compile_mir(mir),
            None => Err("No backend available".to_string()),
        }
    }

    pub fn execute(&mut self, name: &str, args: &[i64]) -> Result<i64, String> {
        match &mut self.cranelift {
            Some(backend) => backend.execute(name, args),
            None => Err("No backend available".to_string()),
        }
    }

    pub fn has_function(&self, name: &str) -> bool {
        match &self.cranelift {
            Some(backend) => backend.has_function(name),
            None => false,
        }
    }

    pub fn list_functions(&self) -> Vec<String> {
        match &self.cranelift {
            Some(backend) => backend.list_functions(),
            None => vec![],
        }
    }

    pub fn set_last_error(&mut self, error: String) {
        self.last_error = error;
    }

    pub fn get_last_error(&self) -> &str {
        &self.last_error
    }
}
```

### FFI Layer (`ffi.rs`)

```rust
// src/runtime/jit/ffi.rs

use super::*;
use super::handles::EXEC_MANAGER_HANDLES;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

// Helper functions
fn string_to_c_char(s: String) -> *const c_char {
    CString::new(s).unwrap().into_raw()
}

fn c_char_to_string(ptr: *const c_char) -> String {
    unsafe { CStr::from_ptr(ptr).to_string_lossy().into_owned() }
}

// JIT Backend Control
#[no_mangle]
pub extern "C" fn rt_set_jit_backend(backend: *const c_char) -> bool {
    let backend_str = c_char_to_string(backend);
    // Set global default (stored in handles module)
    EXEC_MANAGER_HANDLES.lock().unwrap().set_default_backend(backend_str);
    true
}

#[no_mangle]
pub extern "C" fn rt_get_jit_backend() -> *const c_char {
    let handles = EXEC_MANAGER_HANDLES.lock().unwrap();
    let backend = handles.get_default_backend();
    string_to_c_char(backend)
}

// Execution Manager Lifecycle
#[no_mangle]
pub extern "C" fn rt_exec_manager_create(backend: *const c_char) -> i64 {
    let backend_str = c_char_to_string(backend);
    let backend_enum = match backend_str.as_str() {
        "auto" => Backend::Auto,
        "cranelift" => Backend::Cranelift,
        #[cfg(feature = "llvm-jit")]
        "llvm" => Backend::LLVM,
        _ => Backend::Auto,
    };

    match ExecManager::new(backend_enum, 2) {
        Ok(manager) => {
            let mut handles = EXEC_MANAGER_HANDLES.lock().unwrap();
            handles.add(manager)
        }
        Err(_) => 0,
    }
}

#[no_mangle]
pub extern "C" fn rt_exec_manager_cleanup(handle: i64) {
    let mut handles = EXEC_MANAGER_HANDLES.lock().unwrap();
    handles.remove(handle);
}

// Compilation
#[no_mangle]
pub extern "C" fn rt_exec_manager_compile_source(handle: i64, source: *const c_char) -> *const c_char {
    let source_str = c_char_to_string(source);
    let mut handles = EXEC_MANAGER_HANDLES.lock().unwrap();

    if let Some(manager) = handles.get_mut(handle) {
        match manager.compile_source(&source_str) {
            Ok(_) => string_to_c_char(String::new()), // Empty string = success
            Err(e) => string_to_c_char(e),
        }
    } else {
        string_to_c_char("Invalid handle".to_string())
    }
}

#[no_mangle]
pub extern "C" fn rt_exec_manager_compile_mir(handle: i64, mir_data: *const c_char) -> *const c_char {
    // Parse MIR data and compile
    // (Implementation details depend on MIR serialization format)
    string_to_c_char("Not implemented".to_string())
}

#[no_mangle]
pub extern "C" fn rt_exec_manager_compile_file(handle: i64, file_path: *const c_char) -> *const c_char {
    let path = c_char_to_string(file_path);

    // Read file
    let source = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => return string_to_c_char(format!("File error: {}", e)),
    };

    // Use compile_source
    rt_exec_manager_compile_source(handle, string_to_c_char(source))
}

// Execution
#[no_mangle]
pub extern "C" fn rt_exec_manager_execute(handle: i64, name: *const c_char, args: *const i64, args_len: usize) -> i64 {
    let func_name = c_char_to_string(name);
    let args_slice = unsafe { std::slice::from_raw_parts(args, args_len) };

    let mut handles = EXEC_MANAGER_HANDLES.lock().unwrap();
    if let Some(manager) = handles.get_mut(handle) {
        match manager.execute(&func_name, args_slice) {
            Ok(result) => result,
            Err(e) => {
                manager.set_last_error(e);
                0
            }
        }
    } else {
        0
    }
}

// ... (continue with other FFI functions)
```

---

## Integration with Compiler Driver

### Compiler Driver Changes

**Location:** `src/app/compile/driver.spl` or Rust equivalent

**Add JIT Mode:**
```rust
impl CompilerDriver {
    pub fn new_for_jit(opt_level: u8) -> Self {
        Self {
            options: CompileOptions {
                opt_level,
                target: "host".to_string(),
                emit: EmitKind::MIR,  // JIT needs MIR, not object files
                jit_mode: true,       // Skip file I/O
            },
            // ... other fields
        }
    }

    pub fn compile_source(&self, source: &str) -> Result<MIR, String> {
        // Same pipeline as AOT:
        // 1. Lex & Parse
        let ast = self.parse(source)?;

        // 2. Lower to HIR
        let hir = self.lower_to_hir(ast)?;

        // 3. Type check
        self.type_check(&hir)?;

        // 4. Lower to MIR
        let mir = self.lower_to_mir(hir)?;

        // 5. Optimize (if opt_level > 0)
        let optimized_mir = self.optimize(mir)?;

        Ok(optimized_mir)
    }
}
```

**No Code Duplication:** All steps reuse existing AOT compiler code!

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exec_manager_creation() {
        let mgr = ExecManager::new(Backend::Cranelift, 2);
        assert!(mgr.is_ok());
    }

    #[test]
    fn test_simple_compile_and_execute() {
        let mut mgr = ExecManager::new(Backend::Cranelift, 2).unwrap();

        let source = "fn add(x, y): x + y";
        mgr.compile_source(source).unwrap();

        let result = mgr.execute("add", &[10, 32]).unwrap();
        assert_eq!(result, 42);
    }

    #[test]
    fn test_optimization_levels() {
        let mgr0 = ExecManager::new(Backend::Cranelift, 0).unwrap();
        let mgr3 = ExecManager::new(Backend::Cranelift, 3).unwrap();
        // Both should work, just different perf
    }
}
```

### Integration Tests

Run Simple test suite:
```bash
bin/simple test test/app/io/jit_ffi_spec.spl
```

---

## Performance Targets

| Operation | Target | Notes |
|-----------|--------|-------|
| Manager Creation | < 1ms | One-time cost |
| Simple Function Compile | < 10ms | Cranelift, opt=0 |
| Simple Function Execute | < 1μs | Native speed |
| Complex Function Compile | < 100ms | Cranelift, opt=2 |
| LLVM Compile (opt=3) | < 500ms | Best runtime perf |
| Memory Per Manager | < 10MB | Includes compiled code |

---

## Dependencies

**Cargo.toml:**
```toml
[dependencies]
cranelift-jit = "0.98"
cranelift-module = "0.98"
cranelift-native = "0.98"
cranelift-codegen = "0.98"

# Optional LLVM backend
[dependencies.inkwell]
version = "0.2"
features = ["llvm14-0"]
optional = true

[features]
default = ["cranelift-jit"]
llvm-jit = ["inkwell"]
```

---

## Implementation Checklist

### Phase 1: Basic Infrastructure (100 lines)
- [ ] Create `src/runtime/jit/mod.rs`
- [ ] Implement handle management
- [ ] Add backend enum

### Phase 2: Cranelift Integration (300 lines)
- [ ] Create `cranelift_backend.rs`
- [ ] Integrate with existing MIR translator
- [ ] Implement compilation
- [ ] Implement execution

### Phase 3: Compiler Integration (150 lines)
- [ ] Add JIT mode to CompilerDriver
- [ ] Wire up compile_source to use existing pipeline
- [ ] Test with simple functions

### Phase 4: FFI Layer (300 lines)
- [ ] Implement all 20 FFI functions
- [ ] Add string conversion helpers
- [ ] Handle errors properly

### Phase 5: Testing (150 lines)
- [ ] Write unit tests (Rust)
- [ ] Run integration tests (Simple)
- [ ] Benchmark performance

### Phase 6: LLVM Backend (Optional, 200 lines)
- [ ] Create `llvm_backend.rs`
- [ ] Integrate with existing LLVM translator
- [ ] Add feature flag

**Total:** ~1,000 lines Rust (including tests)

**Code Reuse:** ~2,000 lines from existing compiler = **3x smaller than standalone!**

---

## Summary

The JIT wrapper achieves maximum code reuse by:

1. **Parser:** Reuses existing lexer/parser (0 new lines)
2. **Compiler:** Reuses existing HIR/MIR pipeline (0 new lines)
3. **Backend:** Reuses existing MIR→Cranelift/LLVM translators (~50 lines glue)
4. **New Code:** Only handle management and FFI (~800 lines)

**Result:** ~1,000 lines instead of ~3,000 lines, better maintainability, guaranteed consistency with AOT compilation.

**Next Steps:**
1. Implement `cranelift_backend.rs` using existing MIR translator
2. Wire up CompilerDriver for JIT mode
3. Add FFI exports
4. Test and benchmark
