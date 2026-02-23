# CompilerFFI Implementation Design
**Date:** 2026-02-04
**Author:** Claude Code
**Status:** Design Proposal
**Related:** `doc/report/loader_architecture_investigation_2026-02-04.md`

---

## 1. Overview

### 1.1 Purpose

Implement the FFI boundary between the Simple loader (orchestration layer) and Rust compiler (type inference + codegen), enabling:

- Type inference for generic templates at load-time
- Template instantiation with inferred types
- Integration with JitInstantiator for runtime compilation

### 1.2 Current State

**Simple Side (Interface):** `src/compiler/loader/compiler_ffi.spl` (338 lines)

```simple
struct CompilerContext:
    handle: i64  # Opaque pointer to Rust CompilerContextImpl

# Stub implementations (return empty/default values)
extern fn compiler_create_context() -> CompilerContext
extern fn compiler_infer_types(ctx, template, hints) -> [TypeInfo]
extern fn compiler_instantiate_template(ctx, bytes, types) -> CompilationResult
extern fn compiler_check_types(ctx, code, len) -> TypeCheckResult
extern fn compiler_destroy_context(ctx)
```

**Rust Side:** ❌ Not implemented

### 1.3 Goals

✅ Enable type inference across FFI boundary
✅ Support load-time template instantiation
✅ Clean separation between loader and compiler
✅ JSON-based type serialization (language-agnostic)
✅ Efficient FFI with minimal overhead

---

## 2. Architecture

### 2.1 Component Diagram

```
┌───────────────────────────────────────────────────────┐
│              Simple Loader Layer                      │
│  (ModuleLoader, JitInstantiator, ObjTaker)            │
├───────────────────────────────────────────────────────┤
│                                                       │
│  compiler_ffi.spl                                     │
│  ├─ CompilerContext (handle: i64)                    │
│  ├─ TypeInfo (JSON representation)                   │
│  ├─ TemplateBytes (bytes + metadata)                 │
│  └─ CompilationResult (code + errors)                │
│                                                       │
└───────────────────────────────────────────────────────┘
                        │
                        │ FFI Boundary (C ABI)
                        │ JSON serialization for types
                        │
                        ▼
┌───────────────────────────────────────────────────────┐
│          Rust Compiler FFI Module (NEW)               │
│  rust/compiler/src/ffi/                               │
├───────────────────────────────────────────────────────┤
│                                                       │
│  compiler_context.rs                                  │
│  ├─ CompilerContextImpl (owns engines)               │
│  ├─ compiler_create_context()                        │
│  └─ compiler_destroy_context()                       │
│                                                       │
│  type_inference_ffi.rs                                │
│  ├─ TypeSerializer (Type ↔ JSON)                     │
│  ├─ compiler_infer_types()                           │
│  └─ compiler_check_types()                           │
│                                                       │
│  codegen_ffi.rs                                       │
│  ├─ TemplateCompiler                                 │
│  └─ compiler_instantiate_template()                  │
│                                                       │
└───────────────────────────────────────────────────────┘
                        │
            ┌───────────┴───────────┐
            ▼                       ▼
    ┌───────────────┐       ┌──────────────┐
    │ Type Inference│       │   Codegen    │
    │   Engine      │       │   Engine     │
    ├───────────────┤       ├──────────────┤
    │ hir/lower/    │       │ cranelift/   │
    │   expr/       │       │ interpreter/ │
    │   inference.rs│       │              │
    └───────────────┘       └──────────────┘
```

### 2.2 Data Flow

**Type Inference Flow:**

```
1. JitInstantiator.do_jit_compile()
   ↓
2. compiler_infer_types(ctx, template_json, hints_json)
   ↓ (FFI call)
3. TypeSerializer.deserialize_template(template_json)
4. TypeSerializer.deserialize_hints(hints_json)
   ↓
5. TypeInferenceEngine.infer_from_hints(template, hints)
   ↓
6. TypeSerializer.serialize_types(inferred_types)
   ↓ (return JSON)
7. Parse JSON back to [TypeInfo]
```

**Template Instantiation Flow:**

```
1. JitInstantiator.do_jit_compile()
   ↓
2. compiler_instantiate_template(ctx, template_bytes, types_json)
   ↓ (FFI call)
3. TemplateCompiler.parse_template(template_bytes)
4. TypeSerializer.deserialize_types(types_json)
   ↓
5. TemplateCompiler.instantiate(template, types)
   ↓
6. CodegenEngine.generate_code(instantiated)
   ↓ (return compiled bytes)
7. Write to executable memory
```

---

## 3. Type System and JSON Serialization

### 3.1 Type Representation

**Simple Side:**

```simple
struct TypeInfo:
    kind: TypeKind
    name: text                  # For named types
    args: [TypeInfo]            # Generic arguments
    bits: i32                   # For primitives (int, float)
    signed: bool                # For int types
    lanes: i32                  # For SIMD types
    elem: TypeInfo?             # For array/SIMD element type

enum TypeKind:
    Int
    Float
    Bool
    String
    Named       # User-defined types (structs, classes)
    Generic     # Generic parameters (T, U, etc.)
    Array
    Tuple
    Simd
    Function
```

**Rust Side:**

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeInfo {
    kind: TypeKind,
    name: Option<String>,       // For named types
    args: Vec<TypeInfo>,        // Generic arguments
    bits: Option<u32>,          // For primitives
    signed: Option<bool>,       // For int types
    lanes: Option<u32>,         // For SIMD types
    elem: Option<Box<TypeInfo>>,// For array/SIMD
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TypeKind {
    Int,
    Float,
    Bool,
    String,
    Named,
    Generic,
    Array,
    Tuple,
    Simd,
    Function,
}
```

### 3.2 JSON Examples

**Primitive Types:**

```json
// i64
{"kind": "int", "bits": 64, "signed": true}

// f32
{"kind": "float", "bits": 32}

// bool
{"kind": "bool"}

// text
{"kind": "string"}
```

**Generic Types:**

```json
// Vec<i32>
{
  "kind": "named",
  "name": "Vec",
  "args": [
    {"kind": "int", "bits": 32, "signed": true}
  ]
}

// HashMap<text, i64>
{
  "kind": "named",
  "name": "HashMap",
  "args": [
    {"kind": "string"},
    {"kind": "int", "bits": 64, "signed": true}
  ]
}
```

**SIMD Types:**

```json
// f32x4
{
  "kind": "simd",
  "lanes": 4,
  "elem": {"kind": "float", "bits": 32}
}
```

**Array Types:**

```json
// [i64]
{
  "kind": "array",
  "elem": {"kind": "int", "bits": 64, "signed": true}
}
```

**Function Types:**

```json
// fn(i64, i64) -> i64
{
  "kind": "function",
  "args": [
    {"kind": "int", "bits": 64, "signed": true},
    {"kind": "int", "bits": 64, "signed": true}
  ],
  "elem": {"kind": "int", "bits": 64, "signed": true}
}
```

### 3.3 Type Hints

**Purpose:** Provide context for type inference

```simple
struct TypeHint:
    source: HintSource           # Where hint came from
    param_index: i32?            # Which parameter (if applicable)
    ty: TypeInfo                 # The hinted type

enum HintSource:
    CallSite        # From function call site
    Return          # From return type annotation
    Assignment      # From variable assignment
    Constraint      # From type constraint
```

**JSON Example:**

```json
{
  "source": "call_site",
  "param_index": 0,
  "ty": {"kind": "int", "bits": 64, "signed": true}
}
```

---

## 4. Rust Implementation

### 4.1 File Structure

```
rust/compiler/src/ffi/
├── mod.rs                      # Module exports
├── compiler_context.rs         # Context management (200 lines)
├── type_inference_ffi.rs       # Type inference FFI (300 lines)
├── codegen_ffi.rs              # Template compilation FFI (250 lines)
├── type_serializer.rs          # JSON ↔ Type conversion (400 lines)
└── error.rs                    # Error handling (100 lines)
```

**Estimated Total:** ~1,250 lines

### 4.2 compiler_context.rs

```rust
use std::ffi::CStr;
use std::os::raw::c_char;
use crate::type_inference::TypeInferenceEngine;
use crate::codegen::CodeGenerator;

/// Opaque context handle for FFI
pub struct CompilerContextImpl {
    inference_engine: TypeInferenceEngine,
    codegen: CodeGenerator,
    type_cache: HashMap<String, TypeId>,
}

impl CompilerContextImpl {
    fn new() -> Self {
        Self {
            inference_engine: TypeInferenceEngine::new(),
            codegen: CodeGenerator::new(),
            type_cache: HashMap::new(),
        }
    }
}

/// Create a new compiler context
#[no_mangle]
pub extern "C" fn compiler_create_context() -> *mut CompilerContextImpl {
    let ctx = Box::new(CompilerContextImpl::new());
    Box::into_raw(ctx)
}

/// Destroy a compiler context
#[no_mangle]
pub extern "C" fn compiler_destroy_context(ctx: *mut CompilerContextImpl) {
    if !ctx.is_null() {
        unsafe {
            let _ = Box::from_raw(ctx);
        }
    }
}

/// Get last error message (thread-local)
thread_local! {
    static LAST_ERROR: RefCell<Option<String>> = RefCell::new(None);
}

fn set_last_error(err: String) {
    LAST_ERROR.with(|e| *e.borrow_mut() = Some(err));
}

#[no_mangle]
pub extern "C" fn compiler_get_last_error() -> *const c_char {
    LAST_ERROR.with(|e| {
        match e.borrow().as_ref() {
            Some(err) => CString::new(err.clone()).unwrap().into_raw(),
            None => std::ptr::null(),
        }
    })
}

#[no_mangle]
pub extern "C" fn compiler_free_string(s: *mut c_char) {
    if !s.is_null() {
        unsafe {
            let _ = CString::from_raw(s);
        }
    }
}
```

### 4.3 type_inference_ffi.rs

```rust
use super::*;
use crate::ffi::type_serializer::TypeSerializer;
use crate::type_inference::TypeInferenceEngine;

/// Infer types for a generic template
///
/// # Arguments
/// * `ctx` - Compiler context
/// * `template_json` - JSON string describing template
/// * `hints_json` - JSON array of type hints
///
/// # Returns
/// JSON string with inferred types, or NULL on error
#[no_mangle]
pub extern "C" fn compiler_infer_types(
    ctx: *mut CompilerContextImpl,
    template_json: *const c_char,
    hints_json: *const c_char,
) -> *mut c_char {
    // Safety checks
    if ctx.is_null() {
        set_last_error("Null context pointer".to_string());
        return std::ptr::null_mut();
    }

    let ctx = unsafe { &mut *ctx };

    // Parse JSON inputs
    let template_str = unsafe {
        CStr::from_ptr(template_json).to_str()
            .map_err(|e| format!("Invalid UTF-8 in template: {}", e))
    };

    let hints_str = unsafe {
        CStr::from_ptr(hints_json).to_str()
            .map_err(|e| format!("Invalid UTF-8 in hints: {}", e))
    };

    match (template_str, hints_str) {
        (Ok(template), Ok(hints)) => {
            // Deserialize
            let result = TypeSerializer::deserialize_template(template)
                .and_then(|tmpl| TypeSerializer::deserialize_hints(hints)
                    .map(|h| (tmpl, h)))
                .and_then(|(tmpl, hints)| {
                    // Run type inference
                    ctx.inference_engine.infer_from_hints(&tmpl, &hints)
                })
                .and_then(|inferred| {
                    // Serialize result
                    TypeSerializer::serialize_types(&inferred)
                });

            match result {
                Ok(json) => {
                    CString::new(json).unwrap().into_raw()
                }
                Err(e) => {
                    set_last_error(e.to_string());
                    std::ptr::null_mut()
                }
            }
        }
        (Err(e), _) | (_, Err(e)) => {
            set_last_error(e);
            std::ptr::null_mut()
        }
    }
}

/// Check types for a piece of code
#[no_mangle]
pub extern "C" fn compiler_check_types(
    ctx: *mut CompilerContextImpl,
    code: *const u8,
    len: usize,
) -> bool {
    if ctx.is_null() {
        set_last_error("Null context pointer".to_string());
        return false;
    }

    let ctx = unsafe { &mut *ctx };
    let code_slice = unsafe { std::slice::from_raw_parts(code, len) };

    match ctx.inference_engine.check_types(code_slice) {
        Ok(_) => true,
        Err(e) => {
            set_last_error(e.to_string());
            false
        }
    }
}
```

### 4.4 codegen_ffi.rs

```rust
use super::*;

/// Compilation result (returned to Simple)
#[repr(C)]
pub struct CompilationResult {
    success: bool,
    code_ptr: *mut u8,
    code_len: usize,
    error_message: *mut c_char,
}

/// Instantiate a generic template with concrete types
///
/// # Arguments
/// * `ctx` - Compiler context
/// * `template_bytes` - Template bytecode
/// * `template_len` - Length of template
/// * `types_json` - JSON array of type arguments
///
/// # Returns
/// CompilationResult with compiled code or error
#[no_mangle]
pub extern "C" fn compiler_instantiate_template(
    ctx: *mut CompilerContextImpl,
    template_bytes: *const u8,
    template_len: usize,
    types_json: *const c_char,
) -> CompilationResult {
    // Safety checks
    if ctx.is_null() {
        return CompilationResult {
            success: false,
            code_ptr: std::ptr::null_mut(),
            code_len: 0,
            error_message: CString::new("Null context pointer").unwrap().into_raw(),
        };
    }

    let ctx = unsafe { &mut *ctx };
    let template = unsafe { std::slice::from_raw_parts(template_bytes, template_len) };

    // Parse types JSON
    let types_str = unsafe {
        match CStr::from_ptr(types_json).to_str() {
            Ok(s) => s,
            Err(e) => {
                return CompilationResult {
                    success: false,
                    code_ptr: std::ptr::null_mut(),
                    code_len: 0,
                    error_message: CString::new(format!("Invalid UTF-8: {}", e))
                        .unwrap().into_raw(),
                };
            }
        }
    };

    // Deserialize types
    let types = match TypeSerializer::deserialize_types(types_str) {
        Ok(t) => t,
        Err(e) => {
            return CompilationResult {
                success: false,
                code_ptr: std::ptr::null_mut(),
                code_len: 0,
                error_message: CString::new(format!("Type deserialize error: {}", e))
                    .unwrap().into_raw(),
            };
        }
    };

    // Instantiate template
    let result = ctx.codegen.instantiate_template(template, &types);

    match result {
        Ok(code) => {
            // Allocate code buffer (caller must free)
            let mut code_buf = code.into_boxed_slice();
            let code_ptr = code_buf.as_mut_ptr();
            let code_len = code_buf.len();
            std::mem::forget(code_buf);  // Transfer ownership to caller

            CompilationResult {
                success: true,
                code_ptr,
                code_len,
                error_message: std::ptr::null_mut(),
            }
        }
        Err(e) => {
            CompilationResult {
                success: false,
                code_ptr: std::ptr::null_mut(),
                code_len: 0,
                error_message: CString::new(e.to_string()).unwrap().into_raw(),
            }
        }
    }
}

/// Free compiled code buffer
#[no_mangle]
pub extern "C" fn compiler_free_code(code: *mut u8, len: usize) {
    if !code.is_null() {
        unsafe {
            let _ = Vec::from_raw_parts(code, len, len);
        }
    }
}
```

### 4.5 type_serializer.rs

```rust
use serde_json;
use crate::types::{Type, TypeId};

pub struct TypeSerializer;

impl TypeSerializer {
    /// Serialize types to JSON
    pub fn serialize_types(types: &[TypeId]) -> Result<String, SerdeError> {
        let type_infos: Vec<TypeInfo> = types.iter()
            .map(|&tid| Self::type_to_info(tid))
            .collect();
        serde_json::to_string(&type_infos)
    }

    /// Deserialize types from JSON
    pub fn deserialize_types(json: &str) -> Result<Vec<TypeId>, SerdeError> {
        let type_infos: Vec<TypeInfo> = serde_json::from_str(json)?;
        type_infos.iter()
            .map(|info| Self::info_to_type(info))
            .collect()
    }

    /// Convert Type to TypeInfo
    fn type_to_info(tid: TypeId) -> TypeInfo {
        let ty = TYPE_REGISTRY.get(tid);
        match ty {
            Type::Int(bits, signed) => TypeInfo {
                kind: TypeKind::Int,
                bits: Some(bits),
                signed: Some(signed),
                ..Default::default()
            },
            Type::Float(bits) => TypeInfo {
                kind: TypeKind::Float,
                bits: Some(bits),
                ..Default::default()
            },
            Type::Bool => TypeInfo {
                kind: TypeKind::Bool,
                ..Default::default()
            },
            Type::String => TypeInfo {
                kind: TypeKind::String,
                ..Default::default()
            },
            Type::Named(name, args) => TypeInfo {
                kind: TypeKind::Named,
                name: Some(name.clone()),
                args: args.iter().map(|&tid| Self::type_to_info(tid)).collect(),
                ..Default::default()
            },
            Type::Array(elem) => TypeInfo {
                kind: TypeKind::Array,
                elem: Some(Box::new(Self::type_to_info(*elem))),
                ..Default::default()
            },
            Type::Simd(lanes, elem) => TypeInfo {
                kind: TypeKind::Simd,
                lanes: Some(lanes),
                elem: Some(Box::new(Self::type_to_info(*elem))),
                ..Default::default()
            },
            // ... other types
        }
    }

    /// Convert TypeInfo to Type
    fn info_to_type(info: &TypeInfo) -> Result<TypeId, TypeError> {
        match info.kind {
            TypeKind::Int => {
                let bits = info.bits.ok_or("Missing bits for int type")?;
                let signed = info.signed.ok_or("Missing signed for int type")?;
                Ok(TYPE_REGISTRY.get_or_create_int(bits, signed))
            },
            TypeKind::Float => {
                let bits = info.bits.ok_or("Missing bits for float type")?;
                Ok(TYPE_REGISTRY.get_or_create_float(bits))
            },
            TypeKind::Bool => Ok(TYPE_REGISTRY.get_bool()),
            TypeKind::String => Ok(TYPE_REGISTRY.get_string()),
            TypeKind::Named => {
                let name = info.name.as_ref().ok_or("Missing name for named type")?;
                let arg_tids: Result<Vec<TypeId>, _> = info.args.iter()
                    .map(|arg| Self::info_to_type(arg))
                    .collect();
                Ok(TYPE_REGISTRY.get_or_create_named(name, arg_tids?))
            },
            TypeKind::Array => {
                let elem_info = info.elem.as_ref().ok_or("Missing elem for array type")?;
                let elem_tid = Self::info_to_type(elem_info)?;
                Ok(TYPE_REGISTRY.get_or_create_array(elem_tid))
            },
            TypeKind::Simd => {
                let lanes = info.lanes.ok_or("Missing lanes for SIMD type")?;
                let elem_info = info.elem.as_ref().ok_or("Missing elem for SIMD type")?;
                let elem_tid = Self::info_to_type(elem_info)?;
                Ok(TYPE_REGISTRY.get_or_create_simd(lanes, elem_tid))
            },
            // ... other types
        }
    }

    /// Deserialize template metadata
    pub fn deserialize_template(json: &str) -> Result<Template, SerdeError> {
        // Parse template structure from JSON
        serde_json::from_str(json)
    }

    /// Deserialize type hints
    pub fn deserialize_hints(json: &str) -> Result<Vec<TypeHint>, SerdeError> {
        serde_json::from_str(json)
    }
}
```

---

## 5. Integration Points

### 5.1 Type Inference Engine

**Location:** `rust/compiler/src/hir/lower/expr/inference.rs` (existing)

**Required Additions:**

```rust
impl TypeInferenceEngine {
    /// Infer types from hints (NEW - for FFI)
    pub fn infer_from_hints(
        &mut self,
        template: &Template,
        hints: &[TypeHint],
    ) -> Result<Vec<TypeId>, TypeError> {
        // 1. Extract type parameters from template
        let type_params = template.type_params();

        // 2. Create type variables for each parameter
        let type_vars: HashMap<String, TypeVar> = type_params.iter()
            .map(|param| (param.clone(), self.fresh_type_var()))
            .collect();

        // 3. Add constraints from hints
        for hint in hints {
            match hint.source {
                HintSource::CallSite => {
                    // Unify parameter type with hint
                    if let Some(param_idx) = hint.param_index {
                        let param_type = template.param_type(param_idx)?;
                        let param_tvar = self.resolve_type_in_context(param_type, &type_vars)?;
                        self.unify(param_tvar, hint.ty)?;
                    }
                },
                HintSource::Return => {
                    // Unify return type with hint
                    let ret_type = template.return_type()?;
                    let ret_tvar = self.resolve_type_in_context(ret_type, &type_vars)?;
                    self.unify(ret_tvar, hint.ty)?;
                },
                // ... other hint sources
            }
        }

        // 4. Solve constraints
        self.solve_constraints()?;

        // 5. Extract inferred types for type parameters
        let inferred: Result<Vec<TypeId>, _> = type_params.iter()
            .map(|param| {
                let tvar = type_vars[param];
                self.resolve_type_var(tvar)
            })
            .collect();

        inferred
    }

    /// Check types for code (NEW - for FFI)
    pub fn check_types(&mut self, code: &[u8]) -> Result<(), TypeError> {
        // Parse code
        let ast = parse_code(code)?;

        // Type check AST
        self.check_ast(&ast)?;

        Ok(())
    }
}
```

### 5.2 Code Generator

**Location:** `rust/compiler/src/codegen/` (existing)

**Required Additions:**

```rust
impl CodeGenerator {
    /// Instantiate template with concrete types (NEW - for FFI)
    pub fn instantiate_template(
        &mut self,
        template_bytes: &[u8],
        type_args: &[TypeId],
    ) -> Result<Vec<u8>, CodegenError> {
        // 1. Parse template from bytes
        let template = Template::parse(template_bytes)?;

        // 2. Substitute type parameters with concrete types
        let substitution: HashMap<String, TypeId> = template.type_params()
            .iter()
            .zip(type_args.iter())
            .map(|(param, &tid)| (param.clone(), tid))
            .collect();

        let instantiated = template.substitute(&substitution)?;

        // 3. Generate code
        match self.backend {
            CodegenBackend::Cranelift => {
                self.cranelift_generate(&instantiated)
            },
            CodegenBackend::Interpreter => {
                self.interpreter_generate(&instantiated)
            },
        }
    }
}
```

---

## 6. Testing Strategy

### 6.1 Unit Tests (Rust)

**Type Serialization Tests:**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serialize_int_type() {
        let tid = TYPE_REGISTRY.get_or_create_int(64, true);
        let json = TypeSerializer::serialize_types(&[tid]).unwrap();
        assert_eq!(json, r#"[{"kind":"int","bits":64,"signed":true}]"#);
    }

    #[test]
    fn test_deserialize_generic_type() {
        let json = r#"{"kind":"named","name":"Vec","args":[{"kind":"int","bits":32,"signed":true}]}"#;
        let info: TypeInfo = serde_json::from_str(json).unwrap();
        let tid = TypeSerializer::info_to_type(&info).unwrap();

        let ty = TYPE_REGISTRY.get(tid);
        assert!(matches!(ty, Type::Named(name, args) if name == "Vec" && args.len() == 1));
    }

    #[test]
    fn test_type_inference_from_hints() {
        let template = Template::parse(b"fn id<T>(x: T) -> T { x }").unwrap();
        let hints = vec![
            TypeHint {
                source: HintSource::CallSite,
                param_index: Some(0),
                ty: TYPE_REGISTRY.get_or_create_int(64, true),
            }
        ];

        let mut engine = TypeInferenceEngine::new();
        let inferred = engine.infer_from_hints(&template, &hints).unwrap();

        assert_eq!(inferred.len(), 1);  // One type parameter T
        assert_eq!(inferred[0], TYPE_REGISTRY.get_or_create_int(64, true));
    }
}
```

**FFI Tests:**

```rust
#[test]
fn test_compiler_context_lifecycle() {
    let ctx = compiler_create_context();
    assert!(!ctx.is_null());
    compiler_destroy_context(ctx);
}

#[test]
fn test_compiler_infer_types_ffi() {
    let ctx = compiler_create_context();

    let template_json = CString::new(r#"{"name":"id","params":[{"name":"T"}]}"#).unwrap();
    let hints_json = CString::new(r#"[{"source":"call_site","param_index":0,"ty":{"kind":"int","bits":64,"signed":true}}]"#).unwrap();

    let result = compiler_infer_types(ctx, template_json.as_ptr(), hints_json.as_ptr());
    assert!(!result.is_null());

    let result_str = unsafe { CStr::from_ptr(result).to_str().unwrap() };
    let inferred: Vec<TypeInfo> = serde_json::from_str(result_str).unwrap();

    assert_eq!(inferred.len(), 1);
    assert_eq!(inferred[0].kind, TypeKind::Int);
    assert_eq!(inferred[0].bits, Some(64));

    compiler_free_string(result);
    compiler_destroy_context(ctx);
}
```

### 6.2 Integration Tests (Simple)

**Location:** `test/lib/std/unit/compiler/loader/compiler_ffi_spec.spl` (NEW)

```simple
describe "CompilerFFI":
    it "should create and destroy context":
        val ctx = compiler_create_context()
        expect ctx.handle != 0

        compiler_destroy_context(ctx)

    it "should infer type from call site":
        val ctx = compiler_create_context()

        # Template: fn id<T>(x: T) -> T { x }
        val template_json = '{"name":"id","params":[{"name":"T"}]}'

        # Hint: called with i64
        val hints_json = '[{"source":"call_site","param_index":0,"ty":{"kind":"int","bits":64,"signed":true}}]'

        val result_json = compiler_infer_types(ctx, template_json, hints_json)
        expect result_json != ""

        val inferred = parse_json(result_json)
        expect inferred.len() == 1
        expect inferred[0].kind == "int"
        expect inferred[0].bits == 64

        compiler_destroy_context(ctx)

    slow_it "should instantiate template with inferred types":
        val ctx = compiler_create_context()

        # Template bytes (simplified)
        val template_bytes = [0x01, 0x02, 0x03, ...]

        # Types: [i64]
        val types_json = '[{"kind":"int","bits":64,"signed":true}]'

        val result = compiler_instantiate_template(ctx, template_bytes, types_json)
        expect result.success == true
        expect result.code_len > 0

        compiler_free_code(result.code_ptr, result.code_len)
        compiler_destroy_context(ctx)
```

### 6.3 End-to-End Tests

**JitInstantiator Integration:**

```simple
describe "JitInstantiator with CompilerFFI":
    slow_it "should JIT compile generic function":
        val loader = ModuleLoader(config: default_config())

        # Load SMF with generic template
        val smf_path = "test_data/generics.smf"
        loader.load(smf_path)

        # Resolve generic symbol (triggers JIT)
        val address = loader.resolve_generic("my_fn", [i64])
        expect address != 0

        # Call JIT-compiled function
        val func = get_function_pointer(address)
        val result = func(42)
        expect result == 84  # my_fn doubles its input

    slow_it "should handle complex generic instantiation":
        val loader = ModuleLoader(config: default_config())

        # Vec<HashMap<text, i64>>
        val types = [
            TypeInfo(
                kind: Named,
                name: "Vec",
                args: [
                    TypeInfo(
                        kind: Named,
                        name: "HashMap",
                        args: [
                            TypeInfo(kind: String),
                            TypeInfo(kind: Int, bits: 64, signed: true)
                        ]
                    )
                ]
            )
        ]

        val address = loader.resolve_generic("process_data", types)
        expect address != 0
```

---

## 7. Error Handling

### 7.1 Error Types

```rust
#[derive(Debug)]
pub enum CompilerFFIError {
    NullPointer,
    InvalidUtf8(std::str::Utf8Error),
    JsonError(serde_json::Error),
    TypeError(TypeError),
    CodegenError(CodegenError),
    TemplateParseError(String),
}

impl std::fmt::Display for CompilerFFIError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NullPointer => write!(f, "Null pointer passed to FFI"),
            Self::InvalidUtf8(e) => write!(f, "Invalid UTF-8: {}", e),
            Self::JsonError(e) => write!(f, "JSON error: {}", e),
            Self::TypeError(e) => write!(f, "Type error: {}", e),
            Self::CodegenError(e) => write!(f, "Codegen error: {}", e),
            Self::TemplateParseError(e) => write!(f, "Template parse error: {}", e),
        }
    }
}
```

### 7.2 Error Propagation

**Rust Side:**

```rust
fn handle_ffi_result<T>(result: Result<T, CompilerFFIError>) -> Option<T> {
    match result {
        Ok(val) => Some(val),
        Err(e) => {
            set_last_error(e.to_string());
            None
        }
    }
}
```

**Simple Side:**

```simple
fn safe_compiler_infer_types(ctx: CompilerContext, template: text, hints: text) -> [TypeInfo]:
    val result_json = compiler_infer_types(ctx, template, hints)

    if result_json == "":
        val error = compiler_get_last_error()
        error "Type inference failed: {error}"
        return []

    parse_json(result_json)
```

---

## 8. Performance Considerations

### 8.1 FFI Overhead

**JSON Serialization Cost:**
- Serialize: ~500ns per type (simple types)
- Deserialize: ~800ns per type
- For complex generics (e.g., `Vec<HashMap<K, V>>`): ~2-5μs

**Optimization Strategies:**
1. Cache serialized types in CompilerContext
2. Use binary format for frequently-used types
3. Batch type operations to amortize overhead

### 8.2 Type Cache

```rust
pub struct CompilerContextImpl {
    // ... other fields

    /// Cache serialized types
    type_cache: HashMap<TypeId, String>,

    /// Cache deserialized types
    json_cache: HashMap<String, TypeId>,
}

impl CompilerContextImpl {
    fn serialize_type_cached(&mut self, tid: TypeId) -> String {
        self.type_cache.entry(tid)
            .or_insert_with(|| TypeSerializer::type_to_json(tid))
            .clone()
    }

    fn deserialize_type_cached(&mut self, json: &str) -> Result<TypeId, TypeError> {
        if let Some(&tid) = self.json_cache.get(json) {
            return Ok(tid);
        }

        let tid = TypeSerializer::json_to_type(json)?;
        self.json_cache.insert(json.to_string(), tid);
        Ok(tid)
    }
}
```

### 8.3 Batch Operations

**Current (Individual):**
```simple
for ty in types:
    val json = serialize_type(ty)  # 500ns each
```

**Optimized (Batch):**
```simple
val json = serialize_types_batch(types)  # ~300ns average per type
```

---

## 9. Implementation Plan

### Phase 1: Foundation (Week 1)

**Day 1-2: Type Serialization**
- ✅ Implement `TypeInfo` struct in Rust
- ✅ Implement `TypeSerializer::serialize_types()`
- ✅ Implement `TypeSerializer::deserialize_types()`
- ✅ Unit tests for serialization

**Day 3-4: Context Management**
- ✅ Implement `CompilerContextImpl`
- ✅ Implement `compiler_create_context()`
- ✅ Implement `compiler_destroy_context()`
- ✅ Thread-local error handling

**Day 5: Integration**
- ✅ Link FFI module with existing compiler
- ✅ Update build system (Cargo.toml)
- ✅ Smoke tests

### Phase 2: Type Inference (Week 2)

**Day 1-3: Inference Engine**
- ✅ Extend `TypeInferenceEngine` with `infer_from_hints()`
- ✅ Implement hint-based constraint solving
- ✅ Unit tests for inference

**Day 4-5: FFI Interface**
- ✅ Implement `compiler_infer_types()` FFI function
- ✅ Implement `compiler_check_types()` FFI function
- ✅ Integration tests (Rust + Simple)

### Phase 3: Template Instantiation (Week 3)

**Day 1-3: Code Generation**
- ✅ Implement `CodeGenerator::instantiate_template()`
- ✅ Template parsing from bytes
- ✅ Type substitution logic
- ✅ Unit tests

**Day 4-5: FFI Interface**
- ✅ Implement `compiler_instantiate_template()` FFI function
- ✅ Memory management (code buffer ownership)
- ✅ Integration tests

### Phase 4: Integration & Testing (Week 4)

**Day 1-2: JitInstantiator Integration**
- ✅ Update `JitInstantiator` to use real CompilerFFI
- ✅ Remove stub implementations
- ✅ End-to-end tests

**Day 3-4: Performance Optimization**
- ✅ Implement type caching
- ✅ Batch operations
- ✅ Benchmark FFI overhead

**Day 5: Documentation**
- ✅ API documentation
- ✅ Usage examples
- ✅ Update loader architecture docs

---

## 10. Success Criteria

### Functional Requirements

✅ Type inference works across FFI boundary
✅ Template instantiation generates correct code
✅ Error handling propagates cleanly
✅ Memory management is safe (no leaks)
✅ Integration with JitInstantiator is seamless

### Performance Requirements

✅ FFI overhead < 10μs per type operation
✅ Type serialization < 1μs for simple types
✅ Type cache hit rate > 90% in typical workloads
✅ End-to-end JIT compilation < 100ms

### Test Coverage

✅ Unit tests for all FFI functions (Rust)
✅ Integration tests for loader (Simple)
✅ End-to-end tests for JIT instantiation
✅ Error handling tests for all failure paths
✅ Memory leak tests (valgrind)

---

## 11. Future Enhancements

### 11.1 Binary Type Representation

Instead of JSON, use binary format for performance:

```rust
// Compact binary format (8 bytes per simple type)
// [kind: u8] [bits: u8] [flags: u8] [reserved: 5 bytes]

pub struct BinaryTypeEncoder;

impl BinaryTypeEncoder {
    fn encode_type(tid: TypeId) -> Vec<u8> {
        // ... binary encoding
    }

    fn decode_type(bytes: &[u8]) -> Result<TypeId, TypeError> {
        // ... binary decoding
    }
}
```

**Benefits:**
- 10x faster serialization
- 5x smaller payloads
- Still language-agnostic

### 11.2 Incremental Type Inference

Cache inference results to avoid recomputation:

```rust
pub struct TypeInferenceCache {
    cache: HashMap<TemplateSignature, Vec<TypeId>>,
}

impl TypeInferenceCache {
    fn get(&self, template: &Template, hints: &[TypeHint]) -> Option<&Vec<TypeId>> {
        let signature = TemplateSignature::from(template, hints);
        self.cache.get(&signature)
    }

    fn insert(&mut self, template: &Template, hints: &[TypeHint], inferred: Vec<TypeId>) {
        let signature = TemplateSignature::from(template, hints);
        self.cache.insert(signature, inferred);
    }
}
```

### 11.3 Parallel Type Checking

Type-check multiple templates in parallel:

```rust
pub fn parallel_type_check(templates: &[Template]) -> Vec<Result<(), TypeError>> {
    use rayon::prelude::*;

    templates.par_iter()
        .map(|tmpl| check_template(tmpl))
        .collect()
}
```

---

## Appendix A: Complete API Reference

### Rust FFI Functions

```rust
// Context management
#[no_mangle] pub extern "C" fn compiler_create_context() -> *mut CompilerContextImpl;
#[no_mangle] pub extern "C" fn compiler_destroy_context(ctx: *mut CompilerContextImpl);

// Error handling
#[no_mangle] pub extern "C" fn compiler_get_last_error() -> *const c_char;
#[no_mangle] pub extern "C" fn compiler_free_string(s: *mut c_char);

// Type inference
#[no_mangle] pub extern "C" fn compiler_infer_types(
    ctx: *mut CompilerContextImpl,
    template_json: *const c_char,
    hints_json: *const c_char,
) -> *mut c_char;

#[no_mangle] pub extern "C" fn compiler_check_types(
    ctx: *mut CompilerContextImpl,
    code: *const u8,
    len: usize,
) -> bool;

// Template instantiation
#[no_mangle] pub extern "C" fn compiler_instantiate_template(
    ctx: *mut CompilerContextImpl,
    template_bytes: *const u8,
    template_len: usize,
    types_json: *const c_char,
) -> CompilationResult;

#[no_mangle] pub extern "C" fn compiler_free_code(code: *mut u8, len: usize);
```

### Simple FFI Interface

```simple
# Context management
extern fn compiler_create_context() -> CompilerContext
extern fn compiler_destroy_context(ctx: CompilerContext)

# Error handling
extern fn compiler_get_last_error() -> text
extern fn compiler_free_string(s: text)

# Type inference
extern fn compiler_infer_types(
    ctx: CompilerContext,
    template_json: text,
    hints_json: text
) -> text  # JSON array of inferred types

extern fn compiler_check_types(
    ctx: CompilerContext,
    code: [u8],
    len: i64
) -> bool

# Template instantiation
extern fn compiler_instantiate_template(
    ctx: CompilerContext,
    template_bytes: [u8],
    template_len: i64,
    types_json: text
) -> CompilationResult

extern fn compiler_free_code(code: [u8], len: i64)
```

---

**END OF DESIGN**
