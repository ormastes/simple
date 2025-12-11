//! Value types for the interpreter.
//!
//! This module contains the runtime value representation and
//! pointer wrapper types for manual memory management.

use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex, RwLock};

use simple_common::actor::ActorHandle;
use simple_common::manual::{
    Handle as ManualHandle, HandlePool as ManualHandlePool, ManualGc, Shared as ManualShared,
    Unique as ManualUnique, WeakPtr as ManualWeak,
};
use simple_parser::ast::{Expr, FunctionDef};

use crate::error::CompileError;

//==============================================================================
// Magic Names (for formal verification)
//==============================================================================
// These constants define the special names used by the interpreter.
// Making them constants ensures consistency and enables Lean verification.
//
// Lean equivalent:
//   def BUILTIN_RANGE : String := "__range__"
//   def BUILTIN_ARRAY : String := "__array__"
//   def METHOD_NEW : String := "new"
//   def METHOD_SELF : String := "self"
//   def METHOD_MISSING : String := "method_missing"
//   def FUNC_MAIN : String := "main"
//   def ATTR_STRONG : String := "strong"

/// Magic class name for range objects created by range() or `..` syntax
pub const BUILTIN_RANGE: &str = "__range__";

/// Magic class name for array-like objects
pub const BUILTIN_ARRAY: &str = "__array__";

//==============================================================================
// Special Method Names (for formal verification)
//==============================================================================

/// Constructor method name
pub const METHOD_NEW: &str = "new";

/// Self parameter name
pub const METHOD_SELF: &str = "self";

/// Method missing hook name (Ruby-style metaprogramming)
pub const METHOD_MISSING: &str = "method_missing";

/// Entry point function name
pub const FUNC_MAIN: &str = "main";

//==============================================================================
// Special Attribute Names (for formal verification)
//==============================================================================

/// Strong enum attribute (enforces exhaustive matching)
pub const ATTR_STRONG: &str = "strong";

//==============================================================================
// Built-in Type/Function Names (for formal verification)
//==============================================================================

/// Channel constructor name
pub const BUILTIN_CHANNEL: &str = "Channel";

/// Spawn function name for actor creation
pub const BUILTIN_SPAWN: &str = "spawn";

/// User-facing Range class name (alias for BUILTIN_RANGE)
pub const CLASS_RANGE: &str = "Range";

/// User-facing Array class name (alias for BUILTIN_ARRAY)
pub const CLASS_ARRAY: &str = "Array";

//==============================================================================
// Builtin Operation Categories (for formal verification)
//==============================================================================
// These arrays define categories of builtin operations for effect analysis.
// Making them constants enables Lean verification of effect properties.

/// Blocking operations - cannot be used in async contexts
pub const BLOCKING_BUILTINS: &[&str] = &[
    "await", "join", "recv", "sleep", "input", "read_file", "write_file",
];

/// Actor operations - require actor runtime
pub const ACTOR_BUILTINS: &[&str] = &["spawn", "send", "recv", "reply", "join"];

/// Generator operations - require generator runtime
pub const GENERATOR_BUILTINS: &[&str] = &["generator", "next", "collect"];

/// Built-in class types with special handling.
///
/// Lean equivalent:
/// ```lean
/// inductive BuiltinClass
///   | range   -- Range objects (start..end)
///   | array   -- Array-like objects
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinClass {
    /// Range type: represents a range of values
    Range,
    /// Array type: built-in array wrapper
    Array,
}

impl BuiltinClass {
    /// Try to parse a class name as a built-in class.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "__range__" | "Range" => Some(BuiltinClass::Range),
            "__array__" | "Array" => Some(BuiltinClass::Array),
            _ => None,
        }
    }

    /// Get the internal string name of this built-in class.
    pub fn as_str(&self) -> &'static str {
        match self {
            BuiltinClass::Range => BUILTIN_RANGE,
            BuiltinClass::Array => BUILTIN_ARRAY,
        }
    }

    /// Check if the given class name matches this built-in class.
    pub fn matches(&self, name: &str) -> bool {
        match self {
            BuiltinClass::Range => name == BUILTIN_RANGE || name == CLASS_RANGE,
            BuiltinClass::Array => name == BUILTIN_ARRAY || name == CLASS_ARRAY,
        }
    }
}

/// Classification of a class type - either builtin or user-defined.
///
/// Lean equivalent:
/// ```lean
/// inductive ClassType
///   | builtin (b : BuiltinClass)
///   | user (name : String)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassType {
    /// A built-in class with special handling
    Builtin(BuiltinClass),
    /// A user-defined class
    User(String),
}

impl ClassType {
    /// Classify a class name as either builtin or user-defined.
    pub fn from_name(name: &str) -> Self {
        match BuiltinClass::from_name(name) {
            Some(builtin) => ClassType::Builtin(builtin),
            None => ClassType::User(name.to_string()),
        }
    }

    /// Check if this is a built-in class.
    pub fn is_builtin(&self) -> bool {
        matches!(self, ClassType::Builtin(_))
    }

    /// Check if this is the range type.
    pub fn is_range(&self) -> bool {
        matches!(self, ClassType::Builtin(BuiltinClass::Range))
    }
}

//==============================================================================
// Method Lookup (for formal verification)
//==============================================================================
// These types replace magic string "method_missing" with explicit enum variants.
// This makes method dispatch logic verifiable.
// Note: METHOD_MISSING constant is defined above with other special names.

/// Result of looking up a method on a type.
///
/// Lean equivalent:
/// ```lean
/// inductive MethodLookupResult
///   | found           -- Regular method found
///   | notFound        -- Method not found, no fallback
///   | missingHook     -- method_missing fallback available
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MethodLookupResult {
    /// Regular method was found
    Found,
    /// Method not found and no method_missing hook
    NotFound,
    /// Method not found but method_missing hook is available
    MissingHook,
}

impl MethodLookupResult {
    /// Check if a method was found (either direct or via method_missing).
    pub fn is_callable(&self) -> bool {
        matches!(self, MethodLookupResult::Found | MethodLookupResult::MissingHook)
    }

    /// Check if this is the method_missing fallback.
    pub fn is_missing_hook(&self) -> bool {
        matches!(self, MethodLookupResult::MissingHook)
    }
}

/// Variable environment for compile-time evaluation
pub type Env = HashMap<String, Value>;

thread_local! {
    pub(crate) static MANUAL_GC: ManualGc = ManualGc::new();
}

/// NewType for class/struct names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure ClassName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassName(pub String);

impl ClassName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for ClassName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for ClassName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

/// NewType for enum type names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure EnumTypeName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumTypeName(pub String);

impl EnumTypeName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for EnumTypeName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for EnumTypeName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

/// NewType for enum variant names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure VariantName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantName(pub String);

impl VariantName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for VariantName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for VariantName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

//==============================================================================
// Special Enum Types (for formal verification)
//==============================================================================
// These enums replace magic string comparisons for built-in enum types.
// This enables more precise verification and eliminates string-based dispatch.

/// Built-in enum types with special handling.
///
/// Lean equivalent:
/// ```lean
/// inductive SpecialEnumType
///   | option  -- Option<T> (Some/None)
///   | result  -- Result<T, E> (Ok/Err)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialEnumType {
    /// Option type: Some(T) | None
    Option,
    /// Result type: Ok(T) | Err(E)
    Result,
}

impl SpecialEnumType {
    /// Try to parse an enum name as a special enum type.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Option" => Some(SpecialEnumType::Option),
            "Result" => Some(SpecialEnumType::Result),
            _ => None,
        }
    }

    /// Get the string name of this special enum type.
    pub fn as_str(&self) -> &'static str {
        match self {
            SpecialEnumType::Option => "Option",
            SpecialEnumType::Result => "Result",
        }
    }
}

/// Option enum variants.
///
/// Lean equivalent:
/// ```lean
/// inductive OptionVariant
///   | some
///   | none
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptionVariant {
    Some,
    None,
}

impl OptionVariant {
    /// Try to parse a variant name as an Option variant.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Some" => Some(OptionVariant::Some),
            "None" => Some(OptionVariant::None),
            _ => None,
        }
    }

    /// Get the string name of this variant.
    pub fn as_str(&self) -> &'static str {
        match self {
            OptionVariant::Some => "Some",
            OptionVariant::None => "None",
        }
    }
}

/// Result enum variants.
///
/// Lean equivalent:
/// ```lean
/// inductive ResultVariant
///   | ok
///   | err
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResultVariant {
    Ok,
    Err,
}

impl ResultVariant {
    /// Try to parse a variant name as a Result variant.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Ok" => Some(ResultVariant::Ok),
            "Err" => Some(ResultVariant::Err),
            _ => None,
        }
    }

    /// Get the string name of this variant.
    pub fn as_str(&self) -> &'static str {
        match self {
            ResultVariant::Ok => "Ok",
            ResultVariant::Err => "Err",
        }
    }
}

/// Represents the kind of special enum value, combining type and variant.
///
/// Lean equivalent:
/// ```lean
/// inductive SpecialEnumValue
///   | optionSome (payload : Value)
///   | optionNone
///   | resultOk (payload : Value)
///   | resultErr (payload : Value)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialEnumKind {
    /// Option::Some
    OptionSome,
    /// Option::None
    OptionNone,
    /// Result::Ok
    ResultOk,
    /// Result::Err
    ResultErr,
}

impl SpecialEnumKind {
    /// Try to parse enum_name and variant as a special enum kind.
    pub fn from_names(enum_name: &str, variant: &str) -> Option<Self> {
        match (enum_name, variant) {
            ("Option", "Some") => Some(SpecialEnumKind::OptionSome),
            ("Option", "None") => Some(SpecialEnumKind::OptionNone),
            ("Result", "Ok") => Some(SpecialEnumKind::ResultOk),
            ("Result", "Err") => Some(SpecialEnumKind::ResultErr),
            _ => None,
        }
    }

    /// Check if this is an Option variant.
    pub fn is_option(&self) -> bool {
        matches!(self, SpecialEnumKind::OptionSome | SpecialEnumKind::OptionNone)
    }

    /// Check if this is a Result variant.
    pub fn is_result(&self) -> bool {
        matches!(self, SpecialEnumKind::ResultOk | SpecialEnumKind::ResultErr)
    }
}

/// Runtime value representation.
#[derive(Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Symbol(String),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Dict(HashMap<String, Value>),
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
        env: Env,
    },
    /// A function reference - used for decorators and first-class functions
    /// Includes captured environment for closure semantics
    Function {
        name: String,
        def: Box<FunctionDef>,
        captured_env: Env,
    },
    Object {
        class: String,
        fields: HashMap<String, Value>,
    },
    Enum {
        enum_name: String,
        variant: String,
        payload: Option<Box<Value>>,
    },
    /// Constructor reference - a class that can be used to create instances
    /// Used for constructor polymorphism: Constructor[T] type
    Constructor {
        class_name: String,
    },
    Actor(ActorHandle),
    Future(FutureValue),
    Generator(GeneratorValue),
    Channel(ChannelValue),
    ThreadPool(ThreadPoolValue),
    Unique(ManualUniqueValue),
    Shared(ManualSharedValue),
    Weak(ManualWeakValue),
    Handle(ManualHandleValue),
    Borrow(BorrowValue),
    BorrowMut(BorrowMutValue),
    Nil,
}

/// A future that wraps a thread join handle and result
#[derive(Debug)]
pub struct FutureValue {
    result: Arc<Mutex<Option<Result<Value, String>>>>,
    handle: Arc<Mutex<Option<std::thread::JoinHandle<()>>>>,
}

impl FutureValue {
    /// Create a new future from a computation
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce() -> Result<Value, String> + Send + 'static,
    {
        let result: Arc<Mutex<Option<Result<Value, String>>>> = Arc::new(Mutex::new(None));
        let result_clone = result.clone();
        let handle = std::thread::spawn(move || {
            let res = f();
            *result_clone.lock().unwrap() = Some(res);
        });
        FutureValue {
            result,
            handle: Arc::new(Mutex::new(Some(handle))),
        }
    }

    /// Wait for the future to complete and return the result
    pub fn await_result(&self) -> Result<Value, String> {
        // First, join the thread if it's still running
        if let Some(handle) = self.handle.lock().unwrap().take() {
            let _ = handle.join();
        }
        // Then get the result
        self.result
            .lock()
            .unwrap()
            .take()
            .unwrap_or(Err("future result already consumed".to_string()))
    }

    /// Check if the future is completed without blocking
    pub fn is_ready(&self) -> bool {
        self.result.lock().unwrap().is_some()
    }
}

impl Clone for FutureValue {
    fn clone(&self) -> Self {
        FutureValue {
            result: self.result.clone(),
            handle: self.handle.clone(),
        }
    }
}

impl PartialEq for FutureValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.result, &other.result)
    }
}

/// Generator state for stackless coroutines
#[derive(Debug, Clone, PartialEq)]
pub enum GeneratorState {
    /// Initial state, not yet started
    Created,
    /// Suspended at a yield point, waiting to be resumed
    Suspended,
    /// Completed (returned or exhausted)
    Completed,
}

/// A stackless coroutine/generator that can yield values
/// Uses a simple iterator-based model where we collect all yields upfront
#[derive(Debug)]
pub struct GeneratorValue {
    /// Pre-computed yielded values (simple implementation)
    values: Arc<Mutex<Vec<Value>>>,
    /// Current index into values
    index: Arc<Mutex<usize>>,
    /// Current state
    state: Arc<Mutex<GeneratorState>>,
}

impl GeneratorValue {
    /// Create a new generator with pre-computed values
    pub fn new_with_values(values: Vec<Value>) -> Self {
        GeneratorValue {
            values: Arc::new(Mutex::new(values)),
            index: Arc::new(Mutex::new(0)),
            state: Arc::new(Mutex::new(GeneratorState::Created)),
        }
    }

    /// Get the next yielded value
    pub fn next(&self) -> Option<Value> {
        let mut state = self.state.lock().unwrap();
        if *state == GeneratorState::Completed {
            return None;
        }
        *state = GeneratorState::Suspended;
        drop(state);

        let values = self.values.lock().unwrap();
        let mut index = self.index.lock().unwrap();

        if *index < values.len() {
            let val = values[*index].clone();
            *index += 1;

            // Check if exhausted
            if *index >= values.len() {
                drop(index);
                drop(values);
                *self.state.lock().unwrap() = GeneratorState::Completed;
            }

            Some(val)
        } else {
            drop(index);
            drop(values);
            *self.state.lock().unwrap() = GeneratorState::Completed;
            None
        }
    }

    /// Check if the generator is exhausted
    pub fn is_done(&self) -> bool {
        *self.state.lock().unwrap() == GeneratorState::Completed
    }

    /// Collect all remaining values into an array
    pub fn collect_remaining(&self) -> Vec<Value> {
        let mut results = Vec::new();
        while let Some(val) = self.next() {
            results.push(val);
        }
        results
    }
}

impl Clone for GeneratorValue {
    fn clone(&self) -> Self {
        // Share the same underlying state so iteration continues
        GeneratorValue {
            values: self.values.clone(),
            index: self.index.clone(),
            state: self.state.clone(),
        }
    }
}

impl PartialEq for GeneratorValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.values, &other.values)
    }
}

/// A channel for inter-thread communication
#[derive(Debug)]
pub struct ChannelValue {
    sender: std::sync::mpsc::Sender<Value>,
    receiver: Arc<Mutex<std::sync::mpsc::Receiver<Value>>>,
}

impl ChannelValue {
    /// Create a new unbuffered channel
    pub fn new() -> Self {
        let (tx, rx) = std::sync::mpsc::channel();
        ChannelValue {
            sender: tx,
            receiver: Arc::new(Mutex::new(rx)),
        }
    }

    /// Create a new buffered channel with the given capacity
    /// Note: Rust's mpsc doesn't support true buffering, so we just create a regular channel
    /// The capacity is ignored for simplicity
    pub fn with_buffer(_capacity: usize) -> Self {
        // For now, just create a regular unbounded channel
        // True buffering would require a different implementation
        Self::new()
    }

    /// Send a value through the channel
    pub fn send(&self, value: Value) -> Result<(), String> {
        self.sender
            .send(value)
            .map_err(|_| "channel closed".to_string())
    }

    /// Receive a value from the channel (blocking)
    pub fn recv(&self) -> Result<Value, String> {
        self.receiver
            .lock()
            .map_err(|_| "channel lock poisoned".to_string())?
            .recv()
            .map_err(|_| "channel closed".to_string())
    }

    /// Try to receive a value without blocking
    pub fn try_recv(&self) -> Option<Value> {
        self.receiver
            .lock()
            .ok()?
            .try_recv()
            .ok()
    }
}

impl Clone for ChannelValue {
    fn clone(&self) -> Self {
        ChannelValue {
            sender: self.sender.clone(),
            receiver: self.receiver.clone(),
        }
    }
}

impl PartialEq for ChannelValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.receiver, &other.receiver)
    }
}

/// Thread pool for parallel task execution
#[derive(Debug)]
pub struct ThreadPoolValue {
    workers: usize,
}

impl ThreadPoolValue {
    /// Create a new thread pool with the given number of workers
    pub fn new(workers: usize) -> Self {
        ThreadPoolValue { workers }
    }
}

impl Clone for ThreadPoolValue {
    fn clone(&self) -> Self {
        ThreadPoolValue {
            workers: self.workers,
        }
    }
}

impl PartialEq for ThreadPoolValue {
    fn eq(&self, other: &Self) -> bool {
        self.workers == other.workers
    }
}

impl Value {
    pub fn as_int(&self) -> Result<i64, CompileError> {
        match self {
            Value::Int(i) => Ok(*i),
            Value::Float(f) => Ok(*f as i64),
            Value::Bool(b) => Ok(if *b { 1 } else { 0 }),
            Value::Unique(u) => u.inner().as_int(),
            Value::Shared(s) => s.inner().as_int(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).as_int(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).as_int(),
            Value::Borrow(b) => b.inner().as_int(),
            Value::BorrowMut(b) => b.inner().as_int(),
            Value::Str(_) => Err(CompileError::Semantic("expected int, got string".into())),
            Value::Symbol(_) => Err(CompileError::Semantic("expected int, got symbol".into())),
            Value::Nil => Ok(0),
            other => Err(CompileError::Semantic(format!(
                "expected int, got {other:?}"
            ))),
        }
    }

    pub fn as_float(&self) -> Result<f64, CompileError> {
        match self {
            Value::Float(f) => Ok(*f),
            Value::Int(i) => Ok(*i as f64),
            Value::Bool(b) => Ok(if *b { 1.0 } else { 0.0 }),
            Value::Unique(u) => u.inner().as_float(),
            Value::Shared(s) => s.inner().as_float(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).as_float(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).as_float(),
            Value::Borrow(b) => b.inner().as_float(),
            Value::BorrowMut(b) => b.inner().as_float(),
            Value::Nil => Ok(0.0),
            other => Err(CompileError::Semantic(format!(
                "expected float, got {other:?}"
            ))),
        }
    }

    pub fn to_key_string(&self) -> String {
        match self {
            Value::Int(i) => i.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => s.clone(),
            Value::Symbol(s) => s.clone(),
            Value::Unique(u) => u.inner().to_key_string(),
            Value::Shared(s) => s.inner().to_key_string(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).to_key_string(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).to_key_string(),
            Value::Borrow(b) => b.inner().to_key_string(),
            Value::BorrowMut(b) => b.inner().to_key_string(),
            Value::Nil => "nil".to_string(),
            other => format!("{other:?}"),
        }
    }

    pub fn truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0,
            Value::Str(s) => !s.is_empty(),
            Value::Symbol(_) => true,
            Value::Array(a) => !a.is_empty(),
            Value::Tuple(t) => !t.is_empty(),
            Value::Dict(d) => !d.is_empty(),
            Value::Nil => false,
            Value::Unique(u) => u.inner().truthy(),
            Value::Shared(s) => s.inner().truthy(),
            Value::Weak(w) => w.upgrade_inner().map_or(false, |v| v.truthy()),
            Value::Handle(h) => h.resolve_inner().map_or(false, |v| v.truthy()),
            Value::Borrow(b) => b.inner().truthy(),
            Value::BorrowMut(b) => b.inner().truthy(),
            Value::Object { .. }
            | Value::Enum { .. }
            | Value::Lambda { .. }
            | Value::Function { .. }
            | Value::Constructor { .. }
            | Value::Actor(_)
            | Value::Future(_)
            | Value::Generator(_)
            | Value::Channel(_)
            | Value::ThreadPool(_) => true,
        }
    }

    pub fn to_display_string(&self) -> String {
        match self {
            Value::Str(s) => s.clone(),
            Value::Symbol(s) => format!(":{s}"),
            Value::Int(i) => i.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Array(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::Tuple(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("({})", parts.join(", "))
            }
            Value::Dict(map) => {
                let parts: Vec<String> = map
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.to_display_string()))
                    .collect();
                format!("{{{}}}", parts.join(", "))
            }
            Value::Nil => "nil".into(),
            Value::Unique(u) => format!("&{}", u.inner().to_display_string()),
            Value::Shared(s) => format!("*{}", s.inner().to_display_string()),
            Value::Weak(w) => {
                if let Some(v) = w.upgrade_inner() {
                    format!("-{}", v.to_display_string())
                } else {
                    "-<dangling>".into()
                }
            }
            Value::Handle(h) => {
                if let Some(v) = h.resolve_inner() {
                    format!("+{}", v.to_display_string())
                } else {
                    "+<released>".into()
                }
            }
            Value::Borrow(b) => format!("&{}", b.inner().to_display_string()),
            Value::BorrowMut(b) => format!("&mut {}", b.inner().to_display_string()),
            other => format!("{other:?}"),
        }
    }

    /// Convert a unique pointer into its inner value (clone) for read-only operations.
    pub fn deref_pointer(self) -> Value {
        match self {
            Value::Unique(u) => u.into_inner(),
            Value::Shared(s) => s.into_inner(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil),
            Value::Borrow(b) => b.inner().clone(),
            Value::BorrowMut(b) => b.inner().clone(),
            other => other,
        }
    }

    /// Get the runtime type name for this value (used for union type discrimination)
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Int(_) => "i64",
            Value::Float(_) => "f64",
            Value::Bool(_) => "bool",
            Value::Str(_) => "str",
            Value::Symbol(_) => "symbol",
            Value::Array(_) => "array",
            Value::Tuple(_) => "tuple",
            Value::Dict(_) => "dict",
            Value::Lambda { .. } => "function",
            Value::Function { .. } => "function",
            Value::Object { .. } => "object",
            Value::Enum { .. } => "enum",
            Value::Constructor { .. } => "constructor",
            Value::Actor(_) => "actor",
            Value::Future(_) => "future",
            Value::Generator(_) => "generator",
            Value::Channel(_) => "channel",
            Value::ThreadPool(_) => "thread_pool",
            Value::Unique(_) => "unique",
            Value::Shared(_) => "shared",
            Value::Weak(_) => "weak",
            Value::Handle(_) => "handle",
            Value::Borrow(_) => "borrow",
            Value::BorrowMut(_) => "borrow_mut",
            Value::Nil => "nil",
        }
    }

    /// Check if this value matches a given type name (for union type discrimination)
    pub fn matches_type(&self, type_name: &str) -> bool {
        match type_name {
            // Integer types
            "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "Int" => {
                matches!(self, Value::Int(_))
            }
            // Float types
            "f32" | "f64" | "float" | "Float" => {
                matches!(self, Value::Float(_))
            }
            // Boolean
            "bool" | "Bool" => matches!(self, Value::Bool(_)),
            // String types
            "str" | "String" | "Str" => matches!(self, Value::Str(_)),
            // Nil/None
            "nil" | "Nil" | "None" => matches!(self, Value::Nil),
            // Array
            "array" | "Array" => matches!(self, Value::Array(_)),
            // Tuple
            "tuple" | "Tuple" => matches!(self, Value::Tuple(_)),
            // Dict
            "dict" | "Dict" => matches!(self, Value::Dict(_)),
            // Check for object class name
            _ => {
                if let Value::Object { class, .. } = self {
                    class == type_name
                } else if let Value::Enum { enum_name, .. } = self {
                    enum_name == type_name
                } else {
                    false
                }
            }
        }
    }

    // ========================================================================
    // Option/Result enum constructors (reduce duplication across interpreter)
    // ========================================================================

    /// Create Option::Some(value)
    pub fn some(val: Value) -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Option.as_str().into(),
            variant: OptionVariant::Some.as_str().into(),
            payload: Some(Box::new(val)),
        }
    }

    /// Create Option::None
    pub fn none() -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Option.as_str().into(),
            variant: OptionVariant::None.as_str().into(),
            payload: None,
        }
    }

    /// Create Result::Ok(value)
    pub fn ok(val: Value) -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Result.as_str().into(),
            variant: ResultVariant::Ok.as_str().into(),
            payload: Some(Box::new(val)),
        }
    }

    /// Create Result::Err(value)
    pub fn err(val: Value) -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Result.as_str().into(),
            variant: ResultVariant::Err.as_str().into(),
            payload: Some(Box::new(val)),
        }
    }
}

// ============================================================================
// Manual Memory Pointer Wrappers
// ============================================================================

#[derive(Debug)]
pub struct ManualUniqueValue {
    ptr: ManualUnique<Value>,
}

impl ManualUniqueValue {
    pub fn new(value: Value) -> Self {
        MANUAL_GC.with(|gc| Self {
            ptr: gc.alloc(value),
        })
    }

    pub fn inner(&self) -> &Value {
        &self.ptr
    }

    pub fn into_inner(self) -> Value {
        self.ptr.into_inner()
    }
}

impl Clone for ManualUniqueValue {
    fn clone(&self) -> Self {
        // Cloning a unique pointer duplicates the underlying value into a fresh unique owner.
        Self::new((*self.ptr).clone())
    }
}

impl PartialEq for ManualUniqueValue {
    fn eq(&self, other: &Self) -> bool {
        self.inner() == other.inner()
    }
}

#[derive(Debug)]
pub struct ManualSharedValue {
    ptr: ManualShared<Value>,
}

impl ManualSharedValue {
    pub fn new(value: Value) -> Self {
        MANUAL_GC.with(|gc| Self {
            ptr: gc.alloc_shared(value),
        })
    }

    pub fn inner(&self) -> &Value {
        &self.ptr
    }

    pub fn into_inner(self) -> Value {
        (*self.ptr).clone()
    }

    pub fn downgrade(&self) -> ManualWeak<Value> {
        self.ptr.downgrade()
    }
}

impl Clone for ManualSharedValue {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr.clone(),
        }
    }
}

impl PartialEq for ManualSharedValue {
    fn eq(&self, other: &Self) -> bool {
        self.inner() == other.inner()
    }
}

pub struct ManualWeakValue {
    ptr: ManualWeak<Value>,
}

impl fmt::Debug for ManualWeakValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ManualWeakValue")
    }
}

impl ManualWeakValue {
    pub fn new_from_shared(shared: &ManualSharedValue) -> Self {
        Self {
            ptr: shared.downgrade(),
        }
    }

    pub fn upgrade_inner(&self) -> Option<Value> {
        self.ptr.upgrade().map(|s| (*s).clone())
    }
}

impl Clone for ManualWeakValue {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr.clone(),
        }
    }
}

impl PartialEq for ManualWeakValue {
    fn eq(&self, other: &Self) -> bool {
        self.upgrade_inner() == other.upgrade_inner()
    }
}

pub struct ManualHandleValue {
    handle: ManualHandle<Value>,
}

impl fmt::Debug for ManualHandleValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ManualHandleValue")
    }
}

impl ManualHandleValue {
    pub fn new(value: Value) -> Self {
        let pool = ManualHandlePool::new();
        Self {
            handle: pool.alloc(value),
        }
    }

    pub fn resolve_inner(&self) -> Option<Value> {
        self.handle.resolve().map(|v| (*v).clone())
    }
}

impl Clone for ManualHandleValue {
    fn clone(&self) -> Self {
        Self {
            handle: self.handle.clone(),
        }
    }
}

impl PartialEq for ManualHandleValue {
    fn eq(&self, other: &Self) -> bool {
        self.resolve_inner() == other.resolve_inner()
    }
}

// ============================================================================
// Borrow Types (Runtime Borrow Checking)
// ============================================================================

/// Macro to implement common borrow wrapper functionality.
/// Reduces duplication between BorrowValue and BorrowMutValue.
macro_rules! impl_borrow_wrapper {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Debug)]
        pub struct $name {
            /// The borrowed value (shared via Arc + RwLock for thread-safe runtime checking)
            inner: Arc<RwLock<Value>>,
        }

        impl $name {
            pub fn new(value: Value) -> Self {
                Self {
                    inner: Arc::new(RwLock::new(value)),
                }
            }

            pub fn from_arc(arc: Arc<RwLock<Value>>) -> Self {
                Self { inner: arc }
            }

            pub fn inner(&self) -> std::sync::RwLockReadGuard<'_, Value> {
                self.inner.read().unwrap()
            }

            pub fn get_arc(&self) -> Arc<RwLock<Value>> {
                self.inner.clone()
            }
        }

        impl Clone for $name {
            fn clone(&self) -> Self {
                // Cloning a borrow shares the same underlying reference
                Self {
                    inner: self.inner.clone(),
                }
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                *self.inner.read().unwrap() == *other.inner.read().unwrap()
            }
        }
    };
}

impl_borrow_wrapper!(
    BorrowValue,
    "Immutable borrow - uses RwLock for thread-safe runtime borrow checking.\n\
     Multiple immutable borrows are allowed simultaneously."
);

impl_borrow_wrapper!(
    BorrowMutValue,
    "Mutable borrow - uses RwLock for thread-safe runtime borrow checking.\n\
     Only one mutable borrow is allowed at a time (enforced at runtime via RwLock)."
);

// Additional method only for mutable borrows
impl BorrowMutValue {
    pub fn inner_mut(&self) -> std::sync::RwLockWriteGuard<'_, Value> {
        self.inner.write().unwrap()
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::Int(i) => Value::Int(*i),
            Value::Float(f) => Value::Float(*f),
            Value::Bool(b) => Value::Bool(*b),
            Value::Str(s) => Value::Str(s.clone()),
            Value::Symbol(s) => Value::Symbol(s.clone()),
            Value::Array(a) => Value::Array(a.clone()),
            Value::Tuple(t) => Value::Tuple(t.clone()),
            Value::Dict(d) => Value::Dict(d.clone()),
            Value::Lambda { params, body, env } => Value::Lambda {
                params: params.clone(),
                body: body.clone(),
                env: env.clone(),
            },
            Value::Function {
                name,
                def,
                captured_env,
            } => Value::Function {
                name: name.clone(),
                def: def.clone(),
                captured_env: captured_env.clone(),
            },
            Value::Object { class, fields } => Value::Object {
                class: class.clone(),
                fields: fields.clone(),
            },
            Value::Enum {
                enum_name,
                variant,
                payload,
            } => Value::Enum {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
                payload: payload.clone(),
            },
            Value::Constructor { class_name } => Value::Constructor {
                class_name: class_name.clone(),
            },
            Value::Actor(handle) => Value::Actor(handle.clone()),
            Value::Future(f) => Value::Future(f.clone()),
            Value::Generator(g) => Value::Generator(g.clone()),
            Value::Channel(c) => Value::Channel(c.clone()),
            Value::ThreadPool(tp) => Value::ThreadPool(tp.clone()),
            Value::Unique(u) => Value::Unique(u.clone()),
            Value::Shared(s) => Value::Shared(s.clone()),
            Value::Weak(w) => Value::Weak(w.clone()),
            Value::Handle(h) => Value::Handle(h.clone()),
            Value::Borrow(b) => Value::Borrow(b.clone()),
            Value::BorrowMut(b) => Value::BorrowMut(b.clone()),
            Value::Nil => Value::Nil,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => a == b,
            (
                Value::Lambda {
                    params: pa,
                    body: ba,
                    env: ea,
                },
                Value::Lambda {
                    params: pb,
                    body: bb,
                    env: eb,
                },
            ) => pa == pb && ba == bb && ea == eb,
            (
                Value::Function {
                    name: na,
                    def: da,
                    captured_env: ea,
                },
                Value::Function {
                    name: nb,
                    def: db,
                    captured_env: eb,
                },
            ) => na == nb && da == db && ea == eb,
            (
                Value::Object {
                    class: ca,
                    fields: fa,
                },
                Value::Object {
                    class: cb,
                    fields: fb,
                },
            ) => ca == cb && fa == fb,
            (
                Value::Enum {
                    enum_name: ea,
                    variant: va,
                    payload: pa,
                },
                Value::Enum {
                    enum_name: eb,
                    variant: vb,
                    payload: pb,
                },
            ) => ea == eb && va == vb && pa == pb,
            (Value::Constructor { class_name: a }, Value::Constructor { class_name: b }) => a == b,
            (Value::Actor(_), Value::Actor(_)) => true,
            (Value::Future(a), Value::Future(b)) => a == b,
            (Value::Unique(a), Value::Unique(b)) => a == b,
            (Value::Shared(a), Value::Shared(b)) => a == b,
            (Value::Weak(a), Value::Weak(b)) => a == b,
            (Value::Handle(a), Value::Handle(b)) => a == b,
            (Value::Borrow(a), Value::Borrow(b)) => a == b,
            (Value::BorrowMut(a), Value::BorrowMut(b)) => a == b,
            (Value::Nil, Value::Nil) => true,
            _ => false,
        }
    }
}

// Include tests from separate file
include!("value_tests.rs");
