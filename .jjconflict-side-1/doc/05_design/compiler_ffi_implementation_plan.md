# CompilerFFI Implementation Plan - Corrected Architecture
**Date:** 2026-02-04
**Author:** Claude Code
**Status:** Implementation Ready

---

## Architecture Clarification

### What I Misunderstood Initially
❌ Thought we needed to generate Rust FFI code from SFFI specs
❌ Thought unsafe blocks in Simple would implement the FFI

### Actual Architecture (Correct)
✅ **SFFI wrappers are in Simple** - Two-tier pattern (extern fn + wrapper)
✅ **FFI implementations are in Rust** - Direct implementation with #[no_mangle]
✅ **unsafe blocks are in Rust** - For memory operations and pointer handling
✅ **No code generation needed** - Just write Rust implementation directly

---

## Current State Analysis

### Simple Side (Interface) - Already Complete ✅

**Location:** `src/compiler/loader/compiler_ffi.spl` (338 lines)

```simple
struct CompilerContext:
    handle: i64  # Opaque pointer to Rust CompilerContextImpl

# Tier 1: extern fn declarations (FFI boundary)
extern fn compiler_create_context() -> i64
extern fn compiler_destroy_context(handle: i64)
extern fn compiler_infer_types(handle: i64, template_json: text, hints_json: text) -> text
extern fn compiler_instantiate_template(handle: i64, template_bytes: [u8], types_json: text) -> text
extern fn compiler_check_types(handle: i64, code: [u8]) -> bool

# Tier 2: Simple wrapper functions (convenience API)
fn create_compiler() -> CompilerContext:
    CompilerContext(handle: compiler_create_context())

fn infer_types(ctx: CompilerContext, template: text, hints: text) -> [TypeInfo]:
    val result_json = compiler_infer_types(ctx.handle, template, hints)
    parse_type_json(result_json)
```

### Rust Side (Implementation) - Needs Implementation ❌

**Location:** `rust/compiler/src/interpreter_extern/compiler_ffi.rs` (NEW FILE)

**Pattern to Follow:** Same as existing implementations in:
- `rust/compiler/src/interpreter_extern/io/print.rs`
- `rust/compiler/src/interpreter_extern/collections.rs`
- `rust/compiler/src/interpreter_extern/json.rs`

---

## Implementation Pattern (From Existing Code)

### Pattern 1: Simple Values (print.rs style)

```rust
#[no_mangle]
pub extern "C" fn rt_function_name(arg1: i64, arg2: *const u8, arg2_len: usize) -> i64 {
    // Convert raw pointers to Rust types
    let arg2_slice = unsafe { std::slice::from_raw_parts(arg2, arg2_len) };

    // Do work
    let result = do_work(arg1, arg2_slice);

    // Return result
    result
}
```

### Pattern 2: Complex Types with Registry (collections.rs style)

```rust
use once_cell::sync::OnceLock;
use std::sync::{Arc, Mutex};
use std::collections::HashMap as RustHashMap;

// Global registry for opaque handles
static CONTEXT_REGISTRY: OnceLock<Arc<Mutex<RustHashMap<i64, CompilerContextImpl>>>> = OnceLock::new();

fn get_registry() -> Arc<Mutex<RustHashMap<i64, CompilerContextImpl>>> {
    CONTEXT_REGISTRY.get_or_init(|| Arc::new(Mutex::new(RustHashMap::new()))).clone()
}

static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

fn alloc_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn compiler_create_context() -> i64 {
    let ctx = CompilerContextImpl::new();
    let handle = alloc_handle();
    let registry = get_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, ctx);
    handle
}

#[no_mangle]
pub extern "C" fn compiler_destroy_context(handle: i64) {
    let registry = get_registry();
    let mut reg = registry.lock().unwrap();
    reg.remove(&handle);
}
```

### Pattern 3: JSON Serialization (json.rs style)

```rust
#[no_mangle]
pub extern "C" fn rt_json_parse(
    json_ptr: *const u8,
    json_len: usize,
) -> *mut Value {
    let json_bytes = unsafe { std::slice::from_raw_parts(json_ptr, json_len) };
    let json_str = match std::str::from_utf8(json_bytes) {
        Ok(s) => s,
        Err(_) => return Box::into_raw(Box::new(Value::Nil)),
    };

    match serde_json::from_str::<serde_json::Value>(json_str) {
        Ok(parsed) => Box::into_raw(Box::new(json_to_value(&parsed))),
        Err(_) => Box::into_raw(Box::new(Value::Nil)),
    }
}
```

---

## Implementation Steps

### Step 1: Create Rust Module Structure

**File:** `rust/compiler/src/interpreter_extern/compiler_ffi.rs`

```rust
use crate::types::{Type, TypeId};
use crate::hir::lower::expr::inference::TypeInferenceEngine;
use crate::codegen::CodeGenerator;
use once_cell::sync::OnceLock;
use std::sync::{Arc, Mutex, atomic::{AtomicI64, Ordering}};
use std::collections::HashMap as RustHashMap;

/// Internal compiler context implementation
pub struct CompilerContextImpl {
    inference_engine: TypeInferenceEngine,
    codegen: CodeGenerator,
    type_cache: RustHashMap<TypeId, String>,
    json_cache: RustHashMap<String, TypeId>,
}

impl CompilerContextImpl {
    fn new() -> Self {
        Self {
            inference_engine: TypeInferenceEngine::new(),
            codegen: CodeGenerator::new(),
            type_cache: RustHashMap::new(),
            json_cache: RustHashMap::new(),
        }
    }
}

// Registry for opaque handles
static CONTEXT_REGISTRY: OnceLock<Arc<Mutex<RustHashMap<i64, CompilerContextImpl>>>> = OnceLock::new();
static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

fn get_registry() -> Arc<Mutex<RustHashMap<i64, CompilerContextImpl>>> {
    CONTEXT_REGISTRY.get_or_init(|| Arc::new(Mutex::new(RustHashMap::new()))).clone()
}

fn alloc_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}
```

### Step 2: Implement Context Management

```rust
#[no_mangle]
pub extern "C" fn compiler_create_context() -> i64 {
    let ctx = CompilerContextImpl::new();
    let handle = alloc_handle();
    let registry = get_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, ctx);
    handle
}

#[no_mangle]
pub extern "C" fn compiler_destroy_context(handle: i64) {
    let registry = get_registry();
    let mut reg = registry.lock().unwrap();
    reg.remove(&handle);
}
```

### Step 3: Implement Type Inference FFI

```rust
#[no_mangle]
pub extern "C" fn compiler_infer_types(
    handle: i64,
    template_json_ptr: *const u8,
    template_json_len: usize,
    hints_json_ptr: *const u8,
    hints_json_len: usize,
    out_json_ptr: *mut *mut u8,
    out_json_len: *mut usize,
) -> bool {
    // Get context from registry
    let registry = get_registry();
    let mut reg = registry.lock().unwrap();
    let ctx = match reg.get_mut(&handle) {
        Some(c) => c,
        None => return false,
    };

    // Parse JSON inputs
    let template_json = unsafe {
        std::slice::from_raw_parts(template_json_ptr, template_json_len)
    };
    let hints_json = unsafe {
        std::slice::from_raw_parts(hints_json_ptr, hints_json_len)
    };

    let template_str = match std::str::from_utf8(template_json) {
        Ok(s) => s,
        Err(_) => return false,
    };
    let hints_str = match std::str::from_utf8(hints_json) {
        Ok(s) => s,
        Err(_) => return false,
    };

    // Deserialize
    let template: Template = match serde_json::from_str(template_str) {
        Ok(t) => t,
        Err(_) => return false,
    };
    let hints: Vec<TypeHint> = match serde_json::from_str(hints_str) {
        Ok(h) => h,
        Err(_) => return false,
    };

    // Run type inference
    let inferred = match ctx.inference_engine.infer_from_hints(&template, &hints) {
        Ok(types) => types,
        Err(_) => return false,
    };

    // Serialize result
    let type_infos: Vec<TypeInfo> = inferred.iter()
        .map(|&tid| type_to_info(tid))
        .collect();

    let result_json = match serde_json::to_string(&type_infos) {
        Ok(json) => json,
        Err(_) => return false,
    };

    // Allocate output buffer
    let result_bytes = result_json.into_bytes();
    let result_len = result_bytes.len();
    let result_ptr = Box::into_raw(result_bytes.into_boxed_slice()) as *mut u8;

    unsafe {
        *out_json_ptr = result_ptr;
        *out_json_len = result_len;
    }

    true
}
```

### Step 4: Implement Template Instantiation FFI

```rust
#[no_mangle]
pub extern "C" fn compiler_instantiate_template(
    handle: i64,
    template_bytes_ptr: *const u8,
    template_bytes_len: usize,
    types_json_ptr: *const u8,
    types_json_len: usize,
    out_code_ptr: *mut *mut u8,
    out_code_len: *mut usize,
) -> bool {
    // Get context
    let registry = get_registry();
    let mut reg = registry.lock().unwrap();
    let ctx = match reg.get_mut(&handle) {
        Some(c) => c,
        None => return false,
    };

    // Parse inputs
    let template_bytes = unsafe {
        std::slice::from_raw_parts(template_bytes_ptr, template_bytes_len)
    };
    let types_json = unsafe {
        std::slice::from_raw_parts(types_json_ptr, types_json_len)
    };

    let types_str = match std::str::from_utf8(types_json) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let type_infos: Vec<TypeInfo> = match serde_json::from_str(types_str) {
        Ok(t) => t,
        Err(_) => return false,
    };

    let type_ids: Vec<TypeId> = type_infos.iter()
        .filter_map(|info| info_to_type(info).ok())
        .collect();

    // Parse template
    let template = match Template::parse(template_bytes) {
        Ok(t) => t,
        Err(_) => return false,
    };

    // Instantiate
    let code = match ctx.codegen.instantiate_template(&template, &type_ids) {
        Ok(c) => c,
        Err(_) => return false,
    };

    // Return code
    let code_len = code.len();
    let code_ptr = Box::into_raw(code.into_boxed_slice()) as *mut u8;

    unsafe {
        *out_code_ptr = code_ptr;
        *out_code_len = code_len;
    }

    true
}
```

### Step 5: Type Serialization Helpers

```rust
fn type_to_info(tid: TypeId) -> TypeInfo {
    let ty = TYPE_REGISTRY.get(tid);
    match ty {
        Type::Int(bits, signed) => TypeInfo {
            kind: "int".to_string(),
            bits: Some(*bits),
            signed: Some(*signed),
            ..Default::default()
        },
        Type::Float(bits) => TypeInfo {
            kind: "float".to_string(),
            bits: Some(*bits),
            ..Default::default()
        },
        Type::Named(name, args) => TypeInfo {
            kind: "named".to_string(),
            name: Some(name.clone()),
            args: Some(args.iter().map(|&tid| type_to_info(tid)).collect()),
            ..Default::default()
        },
        // ... other types
    }
}

fn info_to_type(info: &TypeInfo) -> Result<TypeId, String> {
    match info.kind.as_str() {
        "int" => {
            let bits = info.bits.ok_or("Missing bits")?;
            let signed = info.signed.ok_or("Missing signed")?;
            Ok(TYPE_REGISTRY.get_or_create_int(bits, signed))
        },
        "float" => {
            let bits = info.bits.ok_or("Missing bits")?;
            Ok(TYPE_REGISTRY.get_or_create_float(bits))
        },
        "named" => {
            let name = info.name.as_ref().ok_or("Missing name")?;
            let args = info.args.as_ref().ok_or("Missing args")?;
            let arg_ids: Result<Vec<TypeId>, _> = args.iter()
                .map(|arg| info_to_type(arg))
                .collect();
            Ok(TYPE_REGISTRY.get_or_create_named(name, arg_ids?))
        },
        _ => Err(format!("Unknown type kind: {}", info.kind)),
    }
}
```

### Step 6: Update Module Exports

**File:** `rust/compiler/src/interpreter_extern/mod.rs`

```rust
pub mod compiler_ffi;

// Re-export public functions
pub use compiler_ffi::{
    compiler_create_context,
    compiler_destroy_context,
    compiler_infer_types,
    compiler_instantiate_template,
};
```

---

## Simplified API (Better Approach)

Instead of complex pointer passing, use **simpler string-based API**:

```rust
// Simpler: Return JSON string directly
#[no_mangle]
pub extern "C" fn compiler_infer_types_simple(
    handle: i64,
    template_json: *const u8,
    template_len: usize,
    hints_json: *const u8,
    hints_len: usize,
) -> *mut u8 {
    // ... parse inputs

    // Run inference
    let inferred = ctx.inference_engine.infer_from_hints(&template, &hints)?;

    // Serialize to JSON
    let result_json = serde_json::to_string(&inferred)?;

    // Return as C string (null-terminated)
    let c_string = std::ffi::CString::new(result_json).unwrap();
    c_string.into_raw() as *mut u8
}

// Free string allocated by Rust
#[no_mangle]
pub extern "C" fn compiler_free_string(ptr: *mut u8) {
    if !ptr.is_null() {
        unsafe {
            let _ = std::ffi::CString::from_raw(ptr as *mut i8);
        }
    }
}
```

**Simple side becomes:**

```simple
extern fn compiler_infer_types_simple(
    handle: i64,
    template_json: text,
    hints_json: text
) -> text

extern fn compiler_free_string(ptr: text)

fn infer_types(ctx: CompilerContext, template: text, hints: text) -> [TypeInfo]:
    val result_json = compiler_infer_types_simple(ctx.handle, template, hints)
    val types = parse_type_json(result_json)
    compiler_free_string(result_json)
    types
```

---

## Testing Strategy

### Unit Tests (Rust)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_lifecycle() {
        let handle = compiler_create_context();
        assert!(handle > 0);
        compiler_destroy_context(handle);
    }

    #[test]
    fn test_type_inference() {
        let handle = compiler_create_context();

        let template_json = r#"{"name":"id","params":[{"name":"T"}]}"#;
        let hints_json = r#"[{"source":"call_site","param_index":0,"ty":{"kind":"int","bits":64,"signed":true}}]"#;

        let result = compiler_infer_types_simple(
            handle,
            template_json.as_ptr(),
            template_json.len(),
            hints_json.as_ptr(),
            hints_json.len(),
        );

        assert!(!result.is_null());

        let result_str = unsafe {
            std::ffi::CStr::from_ptr(result as *const i8)
                .to_str()
                .unwrap()
        };

        let inferred: Vec<TypeInfo> = serde_json::from_str(result_str).unwrap();
        assert_eq!(inferred.len(), 1);

        compiler_free_string(result);
        compiler_destroy_context(handle);
    }
}
```

### Integration Tests (Simple)

**File:** `test/lib/std/unit/compiler/loader/compiler_ffi_spec.spl`

```simple
describe "CompilerFFI":
    it "should create and destroy context":
        val ctx = create_compiler()
        expect ctx.handle > 0
        destroy_compiler(ctx)

    it "should infer type from hint":
        val ctx = create_compiler()

        val template_json = '{"name":"id","params":[{"name":"T"}]}'
        val hints_json = '[{"source":"call_site","param_index":0,"ty":{"kind":"int","bits":64,"signed":true}}]'

        val types = infer_types(ctx, template_json, hints_json)
        expect types.len() == 1
        expect types[0].kind == "int"
        expect types[0].bits == 64

        destroy_compiler(ctx)
```

---

## Summary

### What Needs to Be Done

1. ✅ **Simple side is ready** - Already has extern fn declarations and wrappers
2. ❌ **Rust side needs implementation** - Create `rust/compiler/src/interpreter_extern/compiler_ffi.rs`
3. ❌ **Type inference integration** - Extend TypeInferenceEngine with `infer_from_hints()`
4. ❌ **Codegen integration** - Extend CodeGenerator with `instantiate_template()`
5. ❌ **Testing** - Unit tests in Rust, integration tests in Simple

### Implementation Pattern

- **Follow existing patterns** from `print.rs`, `collections.rs`, `json.rs`
- **Use opaque handles** with global registry (like HashMap in collections.rs)
- **Use JSON for type serialization** across FFI boundary
- **Implement in Rust** with `#[no_mangle]` and `pub extern "C"`
- **No code generation needed** - Direct implementation

### Estimated Effort

- CompilerFFI implementation: ~500 lines Rust
- Type inference extension: ~200 lines Rust
- Codegen extension: ~150 lines Rust
- Tests: ~300 lines (Rust + Simple)
- **Total: ~1,150 lines, ~2-3 days work**

---

**END OF PLAN**
