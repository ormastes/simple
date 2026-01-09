# Function Library Call Plan

## Index

| File | Content |
|------|---------|
| [08_function_lib_call.md](08_function_lib_call.md) | Part 1 |
| [08_function_lib_call_2.md](08_function_lib_call_2.md) | Part 2 |

---


## Overview

Implement function definitions, function calls, and library/module calling conventions for the Simple language.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Function Call System                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │                    Function Types                            │    │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────────┐    │    │
│  │  │ Regular  │ │ Closure  │ │ Method   │ │ External/FFI │    │    │
│  │  │   fn     │ │   \x:    │ │   self.  │ │   extern     │    │    │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────────┘    │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │                    Call Mechanisms                           │    │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────────────┐     │    │
│  │  │   Direct   │  │  Indirect  │  │    Trampoline      │     │    │
│  │  │   (fast)   │  │ (closure)  │  │  (hot-reload)      │     │    │
│  │  └────────────┘  └────────────┘  └────────────────────┘     │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │                    Module System                             │    │
│  │  ┌──────────┐  ┌──────────┐  ┌───────────────────┐          │    │
│  │  │  Import  │  │  Export  │  │  Symbol Resolution │          │    │
│  │  └──────────┘  └──────────┘  └───────────────────┘          │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
crates/runtime/
└── src/
    ├── function/
    │   ├── mod.rs          # Function types
    │   ├── regular.rs      # Regular functions
    │   ├── closure.rs      # Closures with captures
    │   ├── method.rs       # Method dispatch
    │   └── ffi.rs          # External function interface
    ├── call/
    │   ├── mod.rs          # Call conventions
    │   ├── frame.rs        # Call frames
    │   ├── args.rs         # Argument handling
    │   └── dispatch.rs     # Dynamic dispatch
    └── module/
        ├── mod.rs          # Module system
        ├── import.rs       # Import resolution
        └── export.rs       # Export handling
```

---

## Function Types

### Function Value (function/mod.rs)

```rust
// crates/runtime/src/function/mod.rs

mod regular;
mod closure;
mod method;
mod ffi;

pub use regular::*;
pub use closure::*;
pub use method::*;
pub use ffi::*;

use std::rc::Rc;
use crate::value::Value;

/// Function pointer type for native code
pub type NativeFn = unsafe extern "C" fn(*const Value, usize) -> Value;

/// Function value representation
#[derive(Clone)]
pub struct FunctionValue {
    pub name: String,
    pub arity: Arity,
    pub kind: FunctionKind,
    pub effect: Effect,
    pub module: Option<String>,
}

#[derive(Clone)]
pub enum FunctionKind {
    /// Compiled native function (direct call)
    Native(NativeFn),
    /// Compiled with trampoline (hot-reloadable)
    Reloadable(usize),  // Trampoline table index
    /// Closure with captured environment
    Closure(ClosureValue),
    /// External/FFI function
    External(ExternalFn),
    /// Builtin function
    Builtin(BuiltinFn),
}

#[derive(Clone, Copy, Debug)]
pub struct Arity {
    pub required: u8,
    pub optional: u8,
    pub variadic: bool,
}

impl Arity {
    pub fn fixed(n: u8) -> Self {
        Self { required: n, optional: 0, variadic: false }
    }

    pub fn optional(required: u8, optional: u8) -> Self {
        Self { required, optional, variadic: false }
    }

    pub fn variadic(min: u8) -> Self {
        Self { required: min, optional: 0, variadic: true }
    }

    pub fn check(&self, arg_count: usize) -> bool {
        let count = arg_count as u8;
        if self.variadic {
            count >= self.required
        } else {
            count >= self.required && count <= self.required + self.optional
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Effect {
    None,
    Async,
    Async,
}

impl FunctionValue {
    pub fn new_native(name: &str, arity: Arity, ptr: NativeFn) -> Self {
        Self {
            name: name.to_string(),
            arity,
            kind: FunctionKind::Native(ptr),
            effect: Effect::None,
            module: None,
        }
    }

    pub fn new_reloadable(name: &str, arity: Arity, trampoline_id: usize) -> Self {
        Self {
            name: name.to_string(),
            arity,
            kind: FunctionKind::Reloadable(trampoline_id),
            effect: Effect::None,
            module: None,
        }
    }

    pub fn new_builtin(name: &str, arity: Arity, func: BuiltinFn) -> Self {
        Self {
            name: name.to_string(),
            arity,
            kind: FunctionKind::Builtin(func),
            effect: Effect::None,
            module: None,
        }
    }

    pub fn with_effect(mut self, effect: Effect) -> Self {
        self.effect = effect;
        self
    }

    pub fn with_module(mut self, module: &str) -> Self {
        self.module = Some(module.to_string());
        self
    }
}
```

### Regular Functions (function/regular.rs)

```rust
// crates/runtime/src/function/regular.rs

use crate::value::Value;
use super::*;

/// Call a native function directly
pub unsafe fn call_native(func: NativeFn, args: &[Value]) -> Value {
    func(args.as_ptr(), args.len())
}

/// Call through trampoline table (for hot-reload)
pub unsafe fn call_reloadable(trampoline_id: usize, args: &[Value]) -> Value {
    use crate::hotreload::TRAMPOLINES;

    let table = TRAMPOLINES.read().unwrap();
    let ptr = table.get(trampoline_id);
    let func: NativeFn = std::mem::transmute(ptr);
    func(args.as_ptr(), args.len())
}

/// Unified function call
pub fn call_function(func: &FunctionValue, args: &[Value]) -> Result<Value, CallError> {
    // Check arity
    if !func.arity.check(args.len()) {
        return Err(CallError::ArityMismatch {
            expected: func.arity,
            got: args.len(),
        });
    }

    // Dispatch based on kind
    match &func.kind {
        FunctionKind::Native(ptr) => {
            Ok(unsafe { call_native(*ptr, args) })
        }
        FunctionKind::Reloadable(id) => {
            Ok(unsafe { call_reloadable(*id, args) })
        }
        FunctionKind::Closure(closure) => {
            call_closure(closure, args)
        }
        FunctionKind::External(ext) => {
            call_external(ext, args)
        }
        FunctionKind::Builtin(builtin) => {
            Ok(builtin(args))
        }
    }
}

#[derive(Debug)]
pub enum CallError {
    ArityMismatch { expected: Arity, got: usize },
    TypeError { expected: &'static str, got: String },
    RuntimeError(String),
}
```

### Closures (function/closure.rs)

```rust
// crates/runtime/src/function/closure.rs

use std::rc::Rc;
use std::cell::RefCell;
use crate::value::Value;
use super::*;

/// Closure with captured environment
#[derive(Clone)]
pub struct ClosureValue {
    /// The underlying function
    pub func: Rc<FunctionValue>,
    /// Captured variables
    pub captures: Rc<RefCell<Vec<Value>>>,
    /// Capture names (for debugging)
    pub capture_names: Vec<String>,
}

impl ClosureValue {
    pub fn new(
        func: FunctionValue,
        captures: Vec<Value>,
        capture_names: Vec<String>,
    ) -> Self {
        Self {
            func: Rc::new(func),
            captures: Rc::new(RefCell::new(captures)),
            capture_names,
        }
    }

    /// Get captured value by index
    pub fn get_capture(&self, index: usize) -> Option<Value> {
        self.captures.borrow().get(index).cloned()
    }

    /// Set captured value (for mutable captures)
    pub fn set_capture(&self, index: usize, value: Value) {
        if let Some(slot) = self.captures.borrow_mut().get_mut(index) {
            *slot = value;
        }
    }
}

/// Call a closure
pub fn call_closure(closure: &ClosureValue, args: &[Value]) -> Result<Value, CallError> {
    // For native closures, the captures are passed as additional context
    match &closure.func.kind {
        FunctionKind::Native(ptr) => {
            // Build combined args: [captures..., args...]
            let captures = closure.captures.borrow();
            let mut combined = Vec::with_capacity(captures.len() + args.len());
            combined.extend(captures.iter().cloned());
            combined.extend_from_slice(args);

            Ok(unsafe { call_native(*ptr, &combined) })
        }
        _ => {
            // Recursive closure handling
            call_function(&closure.func, args)
        }
    }
}

/// Closure environment frame for compilation
#[derive(Debug)]
pub struct CaptureInfo {
    pub name: String,
    pub index: usize,
    pub is_mutable: bool,
    pub source: CaptureSource,
}

#[derive(Debug, Clone, Copy)]
pub enum CaptureSource {
    /// Captured from enclosing scope
    Local(usize),
    /// Captured from enclosing closure's captures
    Upvalue(usize),
}
```

### Method Dispatch (function/method.rs)

```rust
// crates/runtime/src/function/method.rs

use std::collections::HashMap;
use std::rc::Rc;
use crate::value::Value;
use super::*;

/// Method table for a type
pub struct MethodTable {
    methods: HashMap<String, FunctionValue>,
    type_name: String,
}

impl MethodTable {
    pub fn new(type_name: &str) -> Self {
        Self {
            methods: HashMap::new(),
            type_name: type_name.to_string(),
        }
    }

    pub fn add_method(&mut self, name: &str, func: FunctionValue) {
        self.methods.insert(name.to_string(), func);
    }

    pub fn get_method(&self, name: &str) -> Option<&FunctionValue> {
        self.methods.get(name)
    }
}

/// Global method registry
pub struct MethodRegistry {
    tables: HashMap<String, MethodTable>,
}

impl MethodRegistry {
    pub fn new() -> Self {
        Self { tables: HashMap::new() }
    }

    pub fn register_type(&mut self, type_name: &str) {
        self.tables.insert(
            type_name.to_string(),
            MethodTable::new(type_name),
        );
    }

    pub fn add_method(&mut self, type_name: &str, method_name: &str, func: FunctionValue) {
        if let Some(table) = self.tables.get_mut(type_name) {
            table.add_method(method_name, func);
        }
    }

    pub fn get_method(&self, type_name: &str, method_name: &str) -> Option<&FunctionValue> {
        self.tables.get(type_name)?.get_method(method_name)
    }
}

lazy_static::lazy_static! {
    pub static ref METHODS: std::sync::RwLock<MethodRegistry> =
        std::sync::RwLock::new(MethodRegistry::new());
}

/// Call a method on a value
pub fn call_method(
    receiver: &Value,
    method_name: &str,
    args: &[Value],
) -> Result<Value, CallError> {
    let type_name = receiver.type_tag().name();

    let registry = METHODS.read().unwrap();
    let method = registry.get_method(type_name, method_name)
        .ok_or_else(|| CallError::RuntimeError(
            format!("No method '{}' on type '{}'", method_name, type_name)
        ))?;

    // Prepend receiver to args
    let mut full_args = Vec::with_capacity(args.len() + 1);
    full_args.push(receiver.clone());
    full_args.extend_from_slice(args);

    call_function(method, &full_args)
}
```

### FFI Functions (function/ffi.rs)

```rust
// crates/runtime/src/function/ffi.rs

use std::ffi::CString;
use crate::value::Value;
use super::*;

/// External function from shared library
#[derive(Clone)]
pub struct ExternalFn {
    /// Library handle
    pub library: std::sync::Arc<libloading::Library>,
    /// Symbol name
    pub symbol: String,
    /// Function pointer
    pub ptr: *const (),
    /// Calling convention
    pub convention: CallingConvention,
    /// Parameter types for marshaling
    pub param_types: Vec<FfiType>,
    /// Return type
    pub return_type: FfiType,
}

#[derive(Clone, Copy, Debug)]
pub enum CallingConvention {
    C,          // Standard C calling convention
    System,     // Platform default (stdcall on Windows)
}

#[derive(Clone, Copy, Debug)]
pub enum FfiType {
    Void,
    I8, I16, I32, I64,
    U8, U16, U32, U64,
    F32, F64,
    Ptr,        // Raw pointer
    CString,    // Null-terminated string
}

impl ExternalFn {
    /// Load external function from library
    pub fn load(
        library_path: &str,
        symbol: &str,
        param_types: Vec<FfiType>,
        return_type: FfiType,
    ) -> Result<Self, String> {
        let library = unsafe {
            libloading::Library::new(library_path)
                .map_err(|e| format!("Failed to load library: {}", e))?
        };

        let ptr = unsafe {
            let sym: libloading::Symbol<*const ()> = library.get(symbol.as_bytes())
                .map_err(|e| format!("Failed to find symbol '{}': {}", symbol, e))?;
            *sym
        };

        Ok(Self {
            library: std::sync::Arc::new(library),
            symbol: symbol.to_string(),
            ptr,
            convention: CallingConvention::C,
            param_types,
            return_type,
        })
    }
}

/// Convert Simple value to FFI value
pub fn marshal_to_ffi(value: &Value, ffi_type: FfiType) -> Result<FfiValue, String> {
    match (value, ffi_type) {
        (Value::Int(i), FfiType::I64) => Ok(FfiValue::I64(*i)),
        (Value::Int(i), FfiType::I32) => Ok(FfiValue::I32(*i as i32)),
        (Value::Int(i), FfiType::I16) => Ok(FfiValue::I16(*i as i16)),
        (Value::Int(i), FfiType::I8) => Ok(FfiValue::I8(*i as i8)),
        (Value::Float(f), FfiType::F64) => Ok(FfiValue::F64(*f)),
        (Value::Float(f), FfiType::F32) => Ok(FfiValue::F32(*f as f32)),
        (Value::String(s), FfiType::CString) => {
            let cstr = CString::new(s.as_str())
                .map_err(|_| "String contains null byte")?;
            Ok(FfiValue::CString(cstr))
        }
        (Value::Nil, FfiType::Ptr) => Ok(FfiValue::Ptr(std::ptr::null())),
        _ => Err(format!(
            "Cannot convert {} to {:?}",
            value.type_tag().name(),
            ffi_type
        )),
    }
}

/// Convert FFI value back to Simple value
pub fn marshal_from_ffi(ffi_value: FfiValue, ffi_type: FfiType) -> Value {
    match (ffi_value, ffi_type) {
        (FfiValue::I64(i), _) => Value::Int(i),
        (FfiValue::I32(i), _) => Value::Int(i as i64),
        (FfiValue::F64(f), _) => Value::Float(f),
        (FfiValue::F32(f), _) => Value::Float(f as f64),
        (FfiValue::Void, _) => Value::Nil,
        _ => Value::Nil,
    }
}

#[derive(Clone)]
pub enum FfiValue {
    Void,
    I8(i8), I16(i16), I32(i32), I64(i64),
    U8(u8), U16(u16), U32(u32), U64(u64),
    F32(f32), F64(f64),
    Ptr(*const ()),
    CString(CString),
}

/// Call external function
pub fn call_external(ext: &ExternalFn, args: &[Value]) -> Result<Value, CallError> {
    // Marshal arguments
    let ffi_args: Vec<FfiValue> = args.iter()
        .zip(&ext.param_types)
        .map(|(v, t)| marshal_to_ffi(v, *t))
        .collect::<Result<_, _>>()
        .map_err(|e| CallError::TypeError { expected: "FFI-compatible", got: e })?;

    // Call using libffi or direct invocation
    // This is simplified - real implementation would use libffi
    let result = unsafe {
        call_external_raw(ext.ptr, &ffi_args, ext.return_type)
    };

    Ok(marshal_from_ffi(result, ext.return_type))
}

unsafe fn call_external_raw(
    _ptr: *const (),
    _args: &[FfiValue],
    return_type: FfiType,
) -> FfiValue {
    // Placeholder - real implementation uses libffi
    match return_type {
        FfiType::Void => FfiValue::Void,
        FfiType::I64 => FfiValue::I64(0),
        FfiType::F64 => FfiValue::F64(0.0),
        _ => FfiValue::Void,
    }
}
```

---

## Call Frame Management

### Call Frame (call/frame.rs)

```rust
// crates/runtime/src/call/frame.rs

use crate::value::Value;
use crate::function::FunctionValue;
use std::rc::Rc;

/// Call frame for stack traces and debugging
pub struct CallFrame {
    pub function: Rc<FunctionValue>,
    pub locals: Vec<Value>,
    pub return_addr: usize,
    pub base_pointer: usize,
    pub source_location: Option<SourceLocation>,
}

#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl CallFrame {
    pub fn new(function: Rc<FunctionValue>, arg_count: usize) -> Self {
        Self {
            function,
            locals: Vec::with_capacity(arg_count + 16),  // Args + locals
            return_addr: 0,
            base_pointer: 0,
            source_location: None,
        }
    }

    pub fn get_local(&self, index: usize) -> Option<&Value> {
        self.locals.get(index)
    }

    pub fn set_local(&mut self, index: usize, value: Value) {
        if index < self.locals.len() {
            self.locals[index] = value;
        } else {
            self.locals.resize(index + 1, Value::Nil);
            self.locals[index] = value;
        }
    }
}

/// Call stack for the runtime
pub struct CallStack {
    frames: Vec<CallFrame>,
    max_depth: usize,
}

impl CallStack {
    pub fn new(max_depth: usize) -> Self {
        Self {
            frames: Vec::with_capacity(256),
            max_depth,
        }
    }

    pub fn push(&mut self, frame: CallFrame) -> Result<(), StackOverflowError> {
        if self.frames.len() >= self.max_depth {
            return Err(StackOverflowError {
                depth: self.max_depth,
            });
        }
        self.frames.push(frame);
        Ok(())
    }

    pub fn pop(&mut self) -> Option<CallFrame> {
        self.frames.pop()
    }

    pub fn current(&self) -> Option<&CallFrame> {
        self.frames.last()
    }

    pub fn current_mut(&mut self) -> Option<&mut CallFrame> {
        self.frames.last_mut()
    }

    pub fn depth(&self) -> usize {
---

Next: [Part 2](08_function_lib_call_2.md)
