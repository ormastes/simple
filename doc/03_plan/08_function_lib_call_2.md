# Function Library Call Plan - Part 2

Part of [Function Library Call Plan](08_function_lib_call.md).

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
---

Back to: [Part 1](08_function_lib_call.md)
