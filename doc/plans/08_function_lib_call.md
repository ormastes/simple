# Function and Library Call Plan

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
    Waitless,
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
        self.frames.len()
    }

    /// Generate stack trace
    pub fn stack_trace(&self) -> Vec<StackTraceEntry> {
        self.frames.iter().rev()
            .map(|frame| StackTraceEntry {
                function_name: frame.function.name.clone(),
                module: frame.function.module.clone(),
                location: frame.source_location.clone(),
            })
            .collect()
    }
}

#[derive(Debug)]
pub struct StackOverflowError {
    pub depth: usize,
}

#[derive(Debug)]
pub struct StackTraceEntry {
    pub function_name: String,
    pub module: Option<String>,
    pub location: Option<SourceLocation>,
}

impl std::fmt::Display for StackTraceEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref loc) = self.location {
            write!(f, "  at {} ({}:{}:{})",
                self.function_name,
                loc.file,
                loc.line,
                loc.column
            )
        } else if let Some(ref module) = self.module {
            write!(f, "  at {} ({})", self.function_name, module)
        } else {
            write!(f, "  at {}", self.function_name)
        }
    }
}
```

### Argument Handling (call/args.rs)

```rust
// crates/runtime/src/call/args.rs

use crate::value::Value;
use std::collections::HashMap;

/// Named argument for function calls
pub struct NamedArg {
    pub name: String,
    pub value: Value,
}

/// Argument list for function call
pub struct ArgList {
    positional: Vec<Value>,
    named: HashMap<String, Value>,
}

impl ArgList {
    pub fn new() -> Self {
        Self {
            positional: Vec::new(),
            named: HashMap::new(),
        }
    }

    pub fn positional(args: Vec<Value>) -> Self {
        Self {
            positional: args,
            named: HashMap::new(),
        }
    }

    pub fn push(&mut self, value: Value) {
        self.positional.push(value);
    }

    pub fn push_named(&mut self, name: String, value: Value) {
        self.named.insert(name, value);
    }

    /// Resolve arguments against parameter list
    pub fn resolve(
        self,
        params: &[ParamDef],
    ) -> Result<Vec<Value>, ArgError> {
        let mut result = Vec::with_capacity(params.len());
        let mut positional_iter = self.positional.into_iter();

        for param in params {
            // Try positional first
            if let Some(value) = positional_iter.next() {
                result.push(value);
                continue;
            }

            // Try named
            if let Some(value) = self.named.get(&param.name) {
                result.push(value.clone());
                continue;
            }

            // Try default
            if let Some(ref default) = param.default {
                result.push(default.clone());
                continue;
            }

            // Required parameter missing
            return Err(ArgError::MissingRequired(param.name.clone()));
        }

        // Check for extra positional args
        if positional_iter.next().is_some() {
            return Err(ArgError::TooManyArgs);
        }

        // Check for unknown named args
        for name in self.named.keys() {
            if !params.iter().any(|p| &p.name == name) {
                return Err(ArgError::UnknownNamed(name.clone()));
            }
        }

        Ok(result)
    }
}

#[derive(Debug, Clone)]
pub struct ParamDef {
    pub name: String,
    pub default: Option<Value>,
    pub is_variadic: bool,
}

#[derive(Debug)]
pub enum ArgError {
    MissingRequired(String),
    TooManyArgs,
    UnknownNamed(String),
}
```

---

## Module System

### Module Definition (module/mod.rs)

```rust
// crates/runtime/src/module/mod.rs

mod import;
mod export;

pub use import::*;
pub use export::*;

use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use crate::function::FunctionValue;
use crate::value::Value;

/// A loaded Simple module
pub struct Module {
    pub name: String,
    pub path: Option<PathBuf>,
    pub exports: HashMap<String, Export>,
    pub imports: Vec<Import>,
    pub init_fn: Option<Rc<FunctionValue>>,
}

#[derive(Clone)]
pub enum Export {
    Function(Rc<FunctionValue>),
    Value(Value),
    Type(TypeExport),
}

#[derive(Clone)]
pub struct TypeExport {
    pub name: String,
    pub methods: Vec<String>,
}

impl Module {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            path: None,
            exports: HashMap::new(),
            imports: Vec::new(),
            init_fn: None,
        }
    }

    pub fn export_function(&mut self, name: &str, func: FunctionValue) {
        self.exports.insert(
            name.to_string(),
            Export::Function(Rc::new(func)),
        );
    }

    pub fn export_value(&mut self, name: &str, value: Value) {
        self.exports.insert(
            name.to_string(),
            Export::Value(value),
        );
    }

    pub fn get_export(&self, name: &str) -> Option<&Export> {
        self.exports.get(name)
    }

    pub fn get_function(&self, name: &str) -> Option<Rc<FunctionValue>> {
        match self.exports.get(name)? {
            Export::Function(f) => Some(Rc::clone(f)),
            _ => None,
        }
    }

    /// Run module initialization
    pub fn initialize(&self) -> Result<(), String> {
        if let Some(ref init) = self.init_fn {
            crate::function::call_function(init, &[])
                .map_err(|e| format!("Module init failed: {:?}", e))?;
        }
        Ok(())
    }
}

/// Module registry for loaded modules
pub struct ModuleRegistry {
    modules: HashMap<String, Rc<Module>>,
    search_paths: Vec<PathBuf>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
            search_paths: vec![PathBuf::from(".")],
        }
    }

    pub fn add_search_path(&mut self, path: PathBuf) {
        self.search_paths.push(path);
    }

    pub fn register(&mut self, module: Module) {
        self.modules.insert(module.name.clone(), Rc::new(module));
    }

    pub fn get(&self, name: &str) -> Option<Rc<Module>> {
        self.modules.get(name).cloned()
    }

    /// Resolve module path
    pub fn resolve_path(&self, name: &str) -> Option<PathBuf> {
        let filename = format!("{}.smf", name);

        for search_path in &self.search_paths {
            let path = search_path.join(&filename);
            if path.exists() {
                return Some(path);
            }
        }

        None
    }

    /// Load module by name
    pub fn load(&mut self, name: &str) -> Result<Rc<Module>, String> {
        // Check if already loaded
        if let Some(module) = self.modules.get(name) {
            return Ok(Rc::clone(module));
        }

        // Find module file
        let path = self.resolve_path(name)
            .ok_or_else(|| format!("Module not found: {}", name))?;

        // Load using the loader
        let loaded = crate::loader::ModuleLoader::new()
            .load(&path)
            .map_err(|e| format!("Failed to load {}: {:?}", name, e))?;

        // Create module from loaded data
        let module = self.create_module_from_loaded(name, &loaded)?;
        let rc = Rc::new(module);
        self.modules.insert(name.to_string(), Rc::clone(&rc));

        Ok(rc)
    }

    fn create_module_from_loaded(
        &self,
        name: &str,
        _loaded: &crate::loader::LoadedModule,
    ) -> Result<Module, String> {
        // Convert LoadedModule to runtime Module
        let mut module = Module::new(name);
        // ... populate exports from loaded symbols
        Ok(module)
    }
}

lazy_static::lazy_static! {
    pub static ref MODULES: std::sync::RwLock<ModuleRegistry> =
        std::sync::RwLock::new(ModuleRegistry::new());
}
```

### Import Resolution (module/import.rs)

```rust
// crates/runtime/src/module/import.rs

use super::*;

/// Import declaration
#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub items: ImportItems,
    pub alias: Option<String>,
}

#[derive(Debug, Clone)]
pub enum ImportItems {
    /// import module_name (imports all as module_name.*)
    All,
    /// from module_name import a, b, c
    Named(Vec<ImportItem>),
    /// from module_name import *
    Glob,
}

#[derive(Debug, Clone)]
pub struct ImportItem {
    pub name: String,
    pub alias: Option<String>,
}

impl Import {
    /// import math
    pub fn module(name: &str) -> Self {
        Self {
            module: name.to_string(),
            items: ImportItems::All,
            alias: None,
        }
    }

    /// import math as m
    pub fn module_as(name: &str, alias: &str) -> Self {
        Self {
            module: name.to_string(),
            items: ImportItems::All,
            alias: Some(alias.to_string()),
        }
    }

    /// from math import sin, cos
    pub fn from(module: &str, items: Vec<&str>) -> Self {
        Self {
            module: module.to_string(),
            items: ImportItems::Named(
                items.into_iter()
                    .map(|n| ImportItem { name: n.to_string(), alias: None })
                    .collect()
            ),
            alias: None,
        }
    }

    /// from math import *
    pub fn glob(module: &str) -> Self {
        Self {
            module: module.to_string(),
            items: ImportItems::Glob,
            alias: None,
        }
    }
}

/// Resolve imports for a module
pub fn resolve_imports(
    imports: &[Import],
    registry: &ModuleRegistry,
) -> Result<HashMap<String, Export>, String> {
    let mut resolved = HashMap::new();

    for import in imports {
        let module = registry.get(&import.module)
            .ok_or_else(|| format!("Module not found: {}", import.module))?;

        match &import.items {
            ImportItems::All => {
                // Module namespace import
                let prefix = import.alias.as_ref()
                    .unwrap_or(&import.module);

                for (name, export) in &module.exports {
                    let qualified = format!("{}.{}", prefix, name);
                    resolved.insert(qualified, export.clone());
                }
            }

            ImportItems::Named(items) => {
                for item in items {
                    let export = module.get_export(&item.name)
                        .ok_or_else(|| format!(
                            "{} not found in {}",
                            item.name,
                            import.module
                        ))?;

                    let name = item.alias.as_ref()
                        .unwrap_or(&item.name);

                    resolved.insert(name.clone(), export.clone());
                }
            }

            ImportItems::Glob => {
                for (name, export) in &module.exports {
                    resolved.insert(name.clone(), export.clone());
                }
            }
        }
    }

    Ok(resolved)
}
```

---

## Builtin Functions

### Builtin Registry

```rust
// crates/runtime/src/builtin/mod.rs

use std::collections::HashMap;
use crate::value::Value;
use crate::function::{FunctionValue, BuiltinFn, Arity};

pub type BuiltinFn = fn(&[Value]) -> Value;

pub struct BuiltinRegistry {
    functions: HashMap<String, FunctionValue>,
}

impl BuiltinRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            functions: HashMap::new(),
        };

        // Register all builtins
        registry.register_io();
        registry.register_math();
        registry.register_string();
        registry.register_array();
        registry.register_type();

        registry
    }

    pub fn register(&mut self, name: &str, arity: Arity, func: BuiltinFn) {
        self.functions.insert(
            name.to_string(),
            FunctionValue::new_builtin(name, arity, func),
        );
    }

    pub fn get(&self, name: &str) -> Option<&FunctionValue> {
        self.functions.get(name)
    }

    fn register_io(&mut self) {
        self.register("print", Arity::variadic(0), builtin_print);
        self.register("println", Arity::variadic(0), builtin_println);
        self.register("input", Arity::optional(0, 1), builtin_input);
    }

    fn register_math(&mut self) {
        self.register("abs", Arity::fixed(1), builtin_abs);
        self.register("sqrt", Arity::fixed(1), builtin_sqrt);
        self.register("pow", Arity::fixed(2), builtin_pow);
        self.register("min", Arity::fixed(2), builtin_min);
        self.register("max", Arity::fixed(2), builtin_max);
    }

    fn register_string(&mut self) {
        self.register("str", Arity::fixed(1), builtin_str);
        self.register("len", Arity::fixed(1), builtin_len);
    }

    fn register_array(&mut self) {
        self.register("push", Arity::fixed(2), builtin_push);
        self.register("pop", Arity::fixed(1), builtin_pop);
    }

    fn register_type(&mut self) {
        self.register("type", Arity::fixed(1), builtin_type);
        self.register("is", Arity::fixed(2), builtin_is);
    }
}

// Builtin implementations
fn builtin_print(args: &[Value]) -> Value {
    for (i, arg) in args.iter().enumerate() {
        if i > 0 { print!(" "); }
        print!("{}", arg);
    }
    Value::Nil
}

fn builtin_println(args: &[Value]) -> Value {
    builtin_print(args);
    println!();
    Value::Nil
}

fn builtin_input(args: &[Value]) -> Value {
    if let Some(prompt) = args.first() {
        print!("{}", prompt);
    }
    std::io::Write::flush(&mut std::io::stdout()).ok();

    let mut line = String::new();
    std::io::stdin().read_line(&mut line).ok();

    Value::String(std::rc::Rc::new(
        crate::value::SimpleString::from_string(line.trim_end().to_string())
    ))
}

fn builtin_abs(args: &[Value]) -> Value {
    match args.first() {
        Some(Value::Int(i)) => Value::Int(i.abs()),
        Some(Value::Float(f)) => Value::Float(f.abs()),
        _ => Value::Nil,
    }
}

fn builtin_sqrt(args: &[Value]) -> Value {
    match args.first() {
        Some(Value::Float(f)) => Value::Float(f.sqrt()),
        Some(Value::Int(i)) => Value::Float((*i as f64).sqrt()),
        _ => Value::Nil,
    }
}

fn builtin_pow(args: &[Value]) -> Value {
    match (args.get(0), args.get(1)) {
        (Some(Value::Int(base)), Some(Value::Int(exp))) => {
            if *exp >= 0 {
                Value::Int(base.pow(*exp as u32))
            } else {
                Value::Float((*base as f64).powi(*exp as i32))
            }
        }
        (Some(Value::Float(base)), Some(Value::Float(exp))) => {
            Value::Float(base.powf(*exp))
        }
        _ => Value::Nil,
    }
}

fn builtin_min(args: &[Value]) -> Value {
    match (args.get(0), args.get(1)) {
        (Some(Value::Int(a)), Some(Value::Int(b))) => Value::Int(*a.min(b)),
        (Some(Value::Float(a)), Some(Value::Float(b))) => Value::Float(a.min(*b)),
        _ => Value::Nil,
    }
}

fn builtin_max(args: &[Value]) -> Value {
    match (args.get(0), args.get(1)) {
        (Some(Value::Int(a)), Some(Value::Int(b))) => Value::Int(*a.max(b)),
        (Some(Value::Float(a)), Some(Value::Float(b))) => Value::Float(a.max(*b)),
        _ => Value::Nil,
    }
}

fn builtin_str(args: &[Value]) -> Value {
    match args.first() {
        Some(v) => Value::String(std::rc::Rc::new(
            crate::value::SimpleString::from_string(v.to_string())
        )),
        None => Value::Nil,
    }
}

fn builtin_len(args: &[Value]) -> Value {
    match args.first() {
        Some(Value::String(s)) => Value::Int(s.char_count() as i64),
        Some(Value::Array(arr)) => Value::Int(arr.borrow().len() as i64),
        Some(Value::Tuple(t)) => Value::Int(t.len() as i64),
        Some(Value::Dict(d)) => Value::Int(d.borrow().len() as i64),
        _ => Value::Nil,
    }
}

fn builtin_push(args: &[Value]) -> Value {
    if let (Some(Value::Array(arr)), Some(value)) = (args.get(0), args.get(1)) {
        arr.borrow_mut().push(value.clone());
    }
    Value::Nil
}

fn builtin_pop(args: &[Value]) -> Value {
    if let Some(Value::Array(arr)) = args.first() {
        arr.borrow_mut().pop().unwrap_or(Value::Nil)
    } else {
        Value::Nil
    }
}

fn builtin_type(args: &[Value]) -> Value {
    match args.first() {
        Some(v) => Value::String(std::rc::Rc::new(
            crate::value::SimpleString::new(v.type_tag().name())
        )),
        None => Value::Nil,
    }
}

fn builtin_is(args: &[Value]) -> Value {
    match (args.get(0), args.get(1)) {
        (Some(v), Some(Value::String(type_name))) => {
            Value::Bool(v.type_tag().name() == type_name.as_str())
        }
        _ => Value::Bool(false),
    }
}

lazy_static::lazy_static! {
    pub static ref BUILTINS: BuiltinRegistry = BuiltinRegistry::new();
}
```

---

## Summary

| Component | Purpose |
|-----------|---------|
| `FunctionValue` | Unified function representation |
| `ClosureValue` | Closures with captured environment |
| `ExternalFn` | FFI to C libraries |
| `CallFrame` | Stack frame for debugging |
| `ArgList` | Named/positional argument handling |
| `Module` | Module with exports/imports |
| `BuiltinRegistry` | Standard library functions |

This provides the complete function and module calling infrastructure for the Simple language runtime.
