# Basic Types Implementation Plan

## Overview

Implement the fundamental types for Simple language runtime: i64, f64, bool, char, str, nil, Tuple, Array, and Dict.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Simple Type System                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │                    Primitive Types                           │    │
│  │  ┌─────┐ ┌───────┐ ┌──────┐ ┌──────┐ ┌────────┐ ┌─────┐    │    │
│  │  │ i64 │ │  f64  │ │ bool │ │ char │ │  str   │ │ nil │    │    │
│  │  └─────┘ └───────┘ └──────┘ └──────┘ └────────┘ └─────┘    │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │                    Compound Types                            │    │
│  │  ┌───────────┐ ┌───────────┐ ┌──────────────┐               │    │
│  │  │  Tuple    │ │  Array    │ │    Dict      │               │    │
│  │  │ (T1, T2)  │ │   [T]     │ │  {K: V}      │               │    │
│  │  └───────────┘ └───────────┘ └──────────────┘               │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │                    Value Representation                      │    │
│  │  ┌─────────────────────────────────────────────────────┐    │    │
│  │  │  Tagged Union (NaN-boxing or explicit tag)          │    │    │
│  │  └─────────────────────────────────────────────────────┘    │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
crates/runtime/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── value/
    │   ├── mod.rs          # Value enum
    │   ├── primitive.rs    # i64, f64, bool, char, nil
    │   ├── string.rs       # String type
    │   ├── tuple.rs        # Tuple type
    │   ├── array.rs        # Array type
    │   ├── dict.rs         # Dict type
    │   └── display.rs      # Display/Debug traits
    ├── types/
    │   ├── mod.rs          # Type definitions
    │   ├── typeinfo.rs     # Runtime type info
    │   └── coerce.rs       # Type coercion
    └── memory/
        ├── mod.rs          # Memory management
        └── gc.rs           # GC integration
```

---

## Value Representation

### Strategy: Tagged Union

Use an explicit tagged union for clarity and debugging, with optional NaN-boxing for performance.

### Value Enum (value/mod.rs)

```rust
// crates/runtime/src/value/mod.rs

mod primitive;
mod string;
mod tuple;
mod array;
mod dict;
mod display;

pub use primitive::*;
pub use string::*;
pub use tuple::*;
pub use array::*;
pub use dict::*;

use std::rc::Rc;
use std::cell::RefCell;

/// Runtime value representation
#[derive(Clone)]
pub enum Value {
    // Primitives (unboxed)
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Char(char),

    // Heap-allocated (boxed)
    String(Rc<SimpleString>),
    Symbol(Rc<str>),
    Tuple(Rc<SimpleTuple>),
    Array(Rc<RefCell<SimpleArray>>),
    Dict(Rc<RefCell<SimpleDict>>),

    // References to user types
    Struct(Rc<RefCell<StructInstance>>),
    Enum(Rc<EnumInstance>),
    Function(Rc<FunctionValue>),
    Closure(Rc<ClosureValue>),

    // Actor/Concurrency
    ActorRef(ActorId),
}

impl Value {
    /// Get runtime type tag
    pub fn type_tag(&self) -> TypeTag {
        match self {
            Value::Nil => TypeTag::Nil,
            Value::Bool(_) => TypeTag::Bool,
            Value::Int(_) => TypeTag::Int,
            Value::Float(_) => TypeTag::Float,
            Value::Char(_) => TypeTag::Char,
            Value::String(_) => TypeTag::String,
            Value::Symbol(_) => TypeTag::Symbol,
            Value::Tuple(_) => TypeTag::Tuple,
            Value::Array(_) => TypeTag::Array,
            Value::Dict(_) => TypeTag::Dict,
            Value::Struct(_) => TypeTag::Struct,
            Value::Enum(_) => TypeTag::Enum,
            Value::Function(_) => TypeTag::Function,
            Value::Closure(_) => TypeTag::Closure,
            Value::ActorRef(_) => TypeTag::ActorRef,
        }
    }

    /// Check if value is falsy
    pub fn is_falsy(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Bool(false) => true,
            Value::Int(0) => true,
            Value::Float(f) => *f == 0.0,
            Value::String(s) => s.is_empty(),
            Value::Array(a) => a.borrow().is_empty(),
            _ => false,
        }
    }

    /// Attempt to convert to bool
    pub fn to_bool(&self) -> bool {
        !self.is_falsy()
    }

    /// Attempt to convert to i64
    pub fn to_int(&self) -> Option<i64> {
        match self {
            Value::Int(i) => Some(*i),
            Value::Float(f) => Some(*f as i64),
            Value::Bool(b) => Some(if *b { 1 } else { 0 }),
            Value::Char(c) => Some(*c as i64),
            _ => None,
        }
    }

    /// Attempt to convert to f64
    pub fn to_float(&self) -> Option<f64> {
        match self {
            Value::Float(f) => Some(*f),
            Value::Int(i) => Some(*i as f64),
            _ => None,
        }
    }
}

/// Type tag for runtime type checking
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeTag {
    Nil,
    Bool,
    Int,
    Float,
    Char,
    String,
    Symbol,
    Tuple,
    Array,
    Dict,
    Struct,
    Enum,
    Function,
    Closure,
    ActorRef,
}

impl TypeTag {
    pub fn name(&self) -> &'static str {
        match self {
            TypeTag::Nil => "Nil",
            TypeTag::Bool => "Bool",
            TypeTag::Int => "Int",
            TypeTag::Float => "Float",
            TypeTag::Char => "Char",
            TypeTag::String => "String",
            TypeTag::Symbol => "Symbol",
            TypeTag::Tuple => "Tuple",
            TypeTag::Array => "Array",
            TypeTag::Dict => "Dict",
            TypeTag::Struct => "Struct",
            TypeTag::Enum => "Enum",
            TypeTag::Function => "Function",
            TypeTag::Closure => "Closure",
            TypeTag::ActorRef => "ActorRef",
        }
    }
}
```

---

## Primitive Types

### Primitive Operations (value/primitive.rs)

```rust
// crates/runtime/src/value/primitive.rs

use super::Value;

impl Value {
    // ==================== Int Operations ====================

    pub fn int_add(a: i64, b: i64) -> Value {
        Value::Int(a.wrapping_add(b))
    }

    pub fn int_sub(a: i64, b: i64) -> Value {
        Value::Int(a.wrapping_sub(b))
    }

    pub fn int_mul(a: i64, b: i64) -> Value {
        Value::Int(a.wrapping_mul(b))
    }

    pub fn int_div(a: i64, b: i64) -> Option<Value> {
        if b == 0 {
            None
        } else {
            Some(Value::Int(a / b))
        }
    }

    pub fn int_mod(a: i64, b: i64) -> Option<Value> {
        if b == 0 {
            None
        } else {
            Some(Value::Int(a % b))
        }
    }

    pub fn int_neg(a: i64) -> Value {
        Value::Int(-a)
    }

    pub fn int_pow(base: i64, exp: u32) -> Value {
        Value::Int(base.pow(exp))
    }

    // Bitwise operations
    pub fn int_and(a: i64, b: i64) -> Value {
        Value::Int(a & b)
    }

    pub fn int_or(a: i64, b: i64) -> Value {
        Value::Int(a | b)
    }

    pub fn int_xor(a: i64, b: i64) -> Value {
        Value::Int(a ^ b)
    }

    pub fn int_not(a: i64) -> Value {
        Value::Int(!a)
    }

    pub fn int_shl(a: i64, b: u32) -> Value {
        Value::Int(a << b)
    }

    pub fn int_shr(a: i64, b: u32) -> Value {
        Value::Int(a >> b)
    }

    // Comparison
    pub fn int_eq(a: i64, b: i64) -> Value {
        Value::Bool(a == b)
    }

    pub fn int_lt(a: i64, b: i64) -> Value {
        Value::Bool(a < b)
    }

    pub fn int_le(a: i64, b: i64) -> Value {
        Value::Bool(a <= b)
    }

    pub fn int_gt(a: i64, b: i64) -> Value {
        Value::Bool(a > b)
    }

    pub fn int_ge(a: i64, b: i64) -> Value {
        Value::Bool(a >= b)
    }

    // ==================== Float Operations ====================

    pub fn float_add(a: f64, b: f64) -> Value {
        Value::Float(a + b)
    }

    pub fn float_sub(a: f64, b: f64) -> Value {
        Value::Float(a - b)
    }

    pub fn float_mul(a: f64, b: f64) -> Value {
        Value::Float(a * b)
    }

    pub fn float_div(a: f64, b: f64) -> Value {
        Value::Float(a / b)  // IEEE 754 handles div by zero
    }

    pub fn float_mod(a: f64, b: f64) -> Value {
        Value::Float(a % b)
    }

    pub fn float_neg(a: f64) -> Value {
        Value::Float(-a)
    }

    pub fn float_pow(base: f64, exp: f64) -> Value {
        Value::Float(base.powf(exp))
    }

    // Math functions
    pub fn float_sqrt(a: f64) -> Value {
        Value::Float(a.sqrt())
    }

    pub fn float_abs(a: f64) -> Value {
        Value::Float(a.abs())
    }

    pub fn float_floor(a: f64) -> Value {
        Value::Float(a.floor())
    }

    pub fn float_ceil(a: f64) -> Value {
        Value::Float(a.ceil())
    }

    pub fn float_round(a: f64) -> Value {
        Value::Float(a.round())
    }

    pub fn float_sin(a: f64) -> Value {
        Value::Float(a.sin())
    }

    pub fn float_cos(a: f64) -> Value {
        Value::Float(a.cos())
    }

    // Comparison
    pub fn float_eq(a: f64, b: f64) -> Value {
        Value::Bool(a == b)
    }

    pub fn float_lt(a: f64, b: f64) -> Value {
        Value::Bool(a < b)
    }

    // ==================== Bool Operations ====================

    pub fn bool_and(a: bool, b: bool) -> Value {
        Value::Bool(a && b)
    }

    pub fn bool_or(a: bool, b: bool) -> Value {
        Value::Bool(a || b)
    }

    pub fn bool_not(a: bool) -> Value {
        Value::Bool(!a)
    }

    // ==================== Char Operations ====================

    pub fn char_to_int(c: char) -> Value {
        Value::Int(c as i64)
    }

    pub fn int_to_char(i: i64) -> Option<Value> {
        char::from_u32(i as u32).map(Value::Char)
    }

    pub fn char_is_digit(c: char) -> Value {
        Value::Bool(c.is_ascii_digit())
    }

    pub fn char_is_alpha(c: char) -> Value {
        Value::Bool(c.is_alphabetic())
    }

    pub fn char_is_whitespace(c: char) -> Value {
        Value::Bool(c.is_whitespace())
    }

    pub fn char_to_upper(c: char) -> Value {
        Value::Char(c.to_ascii_uppercase())
    }

    pub fn char_to_lower(c: char) -> Value {
        Value::Char(c.to_ascii_lowercase())
    }
}

/// Parse integer with optional underscore separators
pub fn parse_int(s: &str) -> Option<i64> {
    let s = s.replace('_', "");

    if s.starts_with("0x") || s.starts_with("0X") {
        i64::from_str_radix(&s[2..], 16).ok()
    } else if s.starts_with("0b") || s.starts_with("0B") {
        i64::from_str_radix(&s[2..], 2).ok()
    } else if s.starts_with("0o") || s.starts_with("0O") {
        i64::from_str_radix(&s[2..], 8).ok()
    } else {
        s.parse().ok()
    }
}

/// Parse float
pub fn parse_float(s: &str) -> Option<f64> {
    let s = s.replace('_', "");
    s.parse().ok()
}
```

---

## String Type

### String Implementation (value/string.rs)

```rust
// crates/runtime/src/value/string.rs

use std::rc::Rc;
use std::ops::Deref;
use super::Value;

/// Simple's string type - immutable, UTF-8
#[derive(Debug, Clone)]
pub struct SimpleString {
    data: Rc<str>,
    /// Cached hash for fast comparison
    hash: u64,
}

impl SimpleString {
    pub fn new(s: &str) -> Self {
        Self {
            hash: hash_string(s),
            data: s.into(),
        }
    }

    pub fn from_string(s: String) -> Self {
        let hash = hash_string(&s);
        Self {
            data: s.into(),
            hash,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.data
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn char_count(&self) -> usize {
        self.data.chars().count()
    }

    /// Concatenate two strings
    pub fn concat(&self, other: &SimpleString) -> SimpleString {
        let mut result = String::with_capacity(self.len() + other.len());
        result.push_str(&self.data);
        result.push_str(&other.data);
        SimpleString::from_string(result)
    }

    /// Get character at index (by char, not byte)
    pub fn char_at(&self, index: usize) -> Option<char> {
        self.data.chars().nth(index)
    }

    /// Substring by char indices
    pub fn substring(&self, start: usize, end: usize) -> SimpleString {
        let chars: String = self.data.chars()
            .skip(start)
            .take(end - start)
            .collect();
        SimpleString::from_string(chars)
    }

    /// Split string
    pub fn split(&self, delimiter: &str) -> Vec<SimpleString> {
        self.data.split(delimiter)
            .map(SimpleString::new)
            .collect()
    }

    /// Join strings
    pub fn join(strings: &[SimpleString], separator: &str) -> SimpleString {
        let parts: Vec<&str> = strings.iter().map(|s| s.as_str()).collect();
        SimpleString::from_string(parts.join(separator))
    }

    /// Contains substring
    pub fn contains(&self, needle: &str) -> bool {
        self.data.contains(needle)
    }

    /// Starts with prefix
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.data.starts_with(prefix)
    }

    /// Ends with suffix
    pub fn ends_with(&self, suffix: &str) -> bool {
        self.data.ends_with(suffix)
    }

    /// Find substring
    pub fn find(&self, needle: &str) -> Option<usize> {
        self.data.find(needle)
    }

    /// Replace all occurrences
    pub fn replace(&self, from: &str, to: &str) -> SimpleString {
        SimpleString::from_string(self.data.replace(from, to))
    }

    /// Trim whitespace
    pub fn trim(&self) -> SimpleString {
        SimpleString::new(self.data.trim())
    }

    /// To uppercase
    pub fn to_upper(&self) -> SimpleString {
        SimpleString::from_string(self.data.to_uppercase())
    }

    /// To lowercase
    pub fn to_lower(&self) -> SimpleString {
        SimpleString::from_string(self.data.to_lowercase())
    }

    /// Repeat string
    pub fn repeat(&self, count: usize) -> SimpleString {
        SimpleString::from_string(self.data.repeat(count))
    }

    /// Reverse string
    pub fn reverse(&self) -> SimpleString {
        SimpleString::from_string(self.data.chars().rev().collect())
    }

    /// Get hash for fast comparison
    pub fn hash(&self) -> u64 {
        self.hash
    }
}

impl PartialEq for SimpleString {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: compare hashes first
        if self.hash != other.hash {
            return false;
        }
        self.data == other.data
    }
}

impl Eq for SimpleString {}

impl std::hash::Hash for SimpleString {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl Deref for SimpleString {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

/// FNV-1a hash for strings
fn hash_string(s: &str) -> u64 {
    const FNV_OFFSET: u64 = 14695981039346656037;
    const FNV_PRIME: u64 = 1099511628211;

    let mut hash = FNV_OFFSET;
    for byte in s.bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// String formatting/interpolation
pub fn format_string(template: &str, values: &[(&str, &Value)]) -> SimpleString {
    let mut result = template.to_string();

    for (name, value) in values {
        let placeholder = format!("{{{}}}", name);
        let replacement = value.to_string();
        result = result.replace(&placeholder, &replacement);
    }

    SimpleString::from_string(result)
}

// Value methods for strings
impl Value {
    pub fn string_concat(a: &SimpleString, b: &SimpleString) -> Value {
        Value::String(Rc::new(a.concat(b)))
    }

    pub fn string_len(s: &SimpleString) -> Value {
        Value::Int(s.char_count() as i64)
    }

    pub fn string_eq(a: &SimpleString, b: &SimpleString) -> Value {
        Value::Bool(a == b)
    }
}
```

---

## Tuple Type

### Tuple Implementation (value/tuple.rs)

```rust
// crates/runtime/src/value/tuple.rs

use std::rc::Rc;
use super::Value;

/// Fixed-size heterogeneous collection
#[derive(Debug, Clone)]
pub struct SimpleTuple {
    elements: Vec<Value>,
}

impl SimpleTuple {
    pub fn new(elements: Vec<Value>) -> Self {
        Self { elements }
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Get element at index
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.elements.get(index)
    }

    /// Get element unchecked (for generated code)
    pub unsafe fn get_unchecked(&self, index: usize) -> &Value {
        self.elements.get_unchecked(index)
    }

    /// Iterate elements
    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.elements.iter()
    }

    /// Convert to array
    pub fn to_array(&self) -> Vec<Value> {
        self.elements.clone()
    }

    /// Create unit tuple (empty)
    pub fn unit() -> Self {
        Self { elements: Vec::new() }
    }

    /// Create pair
    pub fn pair(a: Value, b: Value) -> Self {
        Self { elements: vec![a, b] }
    }

    /// Get first element (for pairs)
    pub fn first(&self) -> Option<&Value> {
        self.elements.first()
    }

    /// Get second element (for pairs)
    pub fn second(&self) -> Option<&Value> {
        self.elements.get(1)
    }
}

impl PartialEq for SimpleTuple {
    fn eq(&self, other: &Self) -> bool {
        if self.elements.len() != other.elements.len() {
            return false;
        }

        self.elements.iter()
            .zip(other.elements.iter())
            .all(|(a, b)| values_equal(a, b))
    }
}

fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Nil, Value::Nil) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Char(a), Value::Char(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        (Value::Tuple(a), Value::Tuple(b)) => a == b,
        _ => false,
    }
}

// Value construction helpers
impl Value {
    pub fn tuple(elements: Vec<Value>) -> Value {
        Value::Tuple(Rc::new(SimpleTuple::new(elements)))
    }

    pub fn pair(a: Value, b: Value) -> Value {
        Value::Tuple(Rc::new(SimpleTuple::pair(a, b)))
    }

    pub fn unit() -> Value {
        Value::Tuple(Rc::new(SimpleTuple::unit()))
    }
}
```

---

## Array Type

### Array Implementation (value/array.rs)

```rust
// crates/runtime/src/value/array.rs

use std::rc::Rc;
use std::cell::RefCell;
use super::Value;

/// Growable homogeneous collection (mutable)
#[derive(Debug)]
pub struct SimpleArray {
    elements: Vec<Value>,
}

impl SimpleArray {
    pub fn new() -> Self {
        Self { elements: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self { elements: Vec::with_capacity(capacity) }
    }

    pub fn from_vec(elements: Vec<Value>) -> Self {
        Self { elements }
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    pub fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    // ==================== Access ====================

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.elements.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.elements.get_mut(index)
    }

    pub fn set(&mut self, index: usize, value: Value) -> Option<Value> {
        if index < self.elements.len() {
            Some(std::mem::replace(&mut self.elements[index], value))
        } else {
            None
        }
    }

    pub fn first(&self) -> Option<&Value> {
        self.elements.first()
    }

    pub fn last(&self) -> Option<&Value> {
        self.elements.last()
    }

    // ==================== Modification ====================

    pub fn push(&mut self, value: Value) {
        self.elements.push(value);
    }

    pub fn pop(&mut self) -> Option<Value> {
        self.elements.pop()
    }

    pub fn insert(&mut self, index: usize, value: Value) {
        if index <= self.elements.len() {
            self.elements.insert(index, value);
        }
    }

    pub fn remove(&mut self, index: usize) -> Option<Value> {
        if index < self.elements.len() {
            Some(self.elements.remove(index))
        } else {
            None
        }
    }

    pub fn clear(&mut self) {
        self.elements.clear();
    }

    pub fn extend(&mut self, other: &SimpleArray) {
        self.elements.extend(other.elements.iter().cloned());
    }

    // ==================== Iteration ====================

    pub fn iter(&self) -> impl Iterator<Item = &Value> {
        self.elements.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.elements.iter_mut()
    }

    // ==================== Functional Operations ====================

    pub fn map<F>(&self, f: F) -> SimpleArray
    where
        F: Fn(&Value) -> Value,
    {
        SimpleArray {
            elements: self.elements.iter().map(f).collect(),
        }
    }

    pub fn filter<F>(&self, predicate: F) -> SimpleArray
    where
        F: Fn(&Value) -> bool,
    {
        SimpleArray {
            elements: self.elements.iter()
                .filter(|v| predicate(v))
                .cloned()
                .collect(),
        }
    }

    pub fn reduce<F>(&self, init: Value, f: F) -> Value
    where
        F: Fn(Value, &Value) -> Value,
    {
        self.elements.iter().fold(init, |acc, v| f(acc, v))
    }

    pub fn any<F>(&self, predicate: F) -> bool
    where
        F: Fn(&Value) -> bool,
    {
        self.elements.iter().any(predicate)
    }

    pub fn all<F>(&self, predicate: F) -> bool
    where
        F: Fn(&Value) -> bool,
    {
        self.elements.iter().all(predicate)
    }

    pub fn find<F>(&self, predicate: F) -> Option<&Value>
    where
        F: Fn(&Value) -> bool,
    {
        self.elements.iter().find(|v| predicate(v))
    }

    pub fn position<F>(&self, predicate: F) -> Option<usize>
    where
        F: Fn(&Value) -> bool,
    {
        self.elements.iter().position(|v| predicate(v))
    }

    // ==================== Transformation ====================

    pub fn reverse(&mut self) {
        self.elements.reverse();
    }

    pub fn reversed(&self) -> SimpleArray {
        let mut elements = self.elements.clone();
        elements.reverse();
        SimpleArray { elements }
    }

    pub fn sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&Value, &Value) -> std::cmp::Ordering,
    {
        self.elements.sort_by(compare);
    }

    pub fn slice(&self, start: usize, end: usize) -> SimpleArray {
        let end = end.min(self.elements.len());
        let start = start.min(end);
        SimpleArray {
            elements: self.elements[start..end].to_vec(),
        }
    }

    pub fn concat(&self, other: &SimpleArray) -> SimpleArray {
        let mut elements = self.elements.clone();
        elements.extend(other.elements.iter().cloned());
        SimpleArray { elements }
    }

    // ==================== Utility ====================

    pub fn contains(&self, value: &Value) -> bool {
        self.elements.iter().any(|v| values_equal(v, value))
    }

    pub fn clone_elements(&self) -> Vec<Value> {
        self.elements.clone()
    }
}

fn values_equal(a: &Value, b: &Value) -> bool {
    // Same as in tuple.rs
    match (a, b) {
        (Value::Nil, Value::Nil) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Char(a), Value::Char(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        _ => false,
    }
}

// Value helpers
impl Value {
    pub fn array(elements: Vec<Value>) -> Value {
        Value::Array(Rc::new(RefCell::new(SimpleArray::from_vec(elements))))
    }

    pub fn empty_array() -> Value {
        Value::Array(Rc::new(RefCell::new(SimpleArray::new())))
    }

    pub fn array_len(arr: &Rc<RefCell<SimpleArray>>) -> Value {
        Value::Int(arr.borrow().len() as i64)
    }
}
```

---

## Dict Type

### Dict Implementation (value/dict.rs)

```rust
// crates/runtime/src/value/dict.rs

use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use super::Value;

/// Key type for Dict - must be hashable
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DictKey {
    Int(i64),
    String(Rc<str>),
    Bool(bool),
    Char(char),
}

impl DictKey {
    pub fn from_value(value: &Value) -> Option<Self> {
        match value {
            Value::Int(i) => Some(DictKey::Int(*i)),
            Value::String(s) => Some(DictKey::String(s.as_str().into())),
            Value::Bool(b) => Some(DictKey::Bool(*b)),
            Value::Char(c) => Some(DictKey::Char(*c)),
            _ => None,
        }
    }

    pub fn to_value(&self) -> Value {
        match self {
            DictKey::Int(i) => Value::Int(*i),
            DictKey::String(s) => Value::String(Rc::new(super::SimpleString::new(s))),
            DictKey::Bool(b) => Value::Bool(*b),
            DictKey::Char(c) => Value::Char(*c),
        }
    }
}

/// Dictionary/Map type
#[derive(Debug)]
pub struct SimpleDict {
    entries: HashMap<DictKey, Value>,
}

impl SimpleDict {
    pub fn new() -> Self {
        Self { entries: HashMap::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self { entries: HashMap::with_capacity(capacity) }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    // ==================== Access ====================

    pub fn get(&self, key: &DictKey) -> Option<&Value> {
        self.entries.get(key)
    }

    pub fn get_value(&self, key: &Value) -> Option<&Value> {
        DictKey::from_value(key).and_then(|k| self.entries.get(&k))
    }

    pub fn contains_key(&self, key: &DictKey) -> bool {
        self.entries.contains_key(key)
    }

    // ==================== Modification ====================

    pub fn insert(&mut self, key: DictKey, value: Value) -> Option<Value> {
        self.entries.insert(key, value)
    }

    pub fn insert_value(&mut self, key: &Value, value: Value) -> Option<Value> {
        DictKey::from_value(key).and_then(|k| self.entries.insert(k, value))
    }

    pub fn remove(&mut self, key: &DictKey) -> Option<Value> {
        self.entries.remove(key)
    }

    pub fn remove_value(&mut self, key: &Value) -> Option<Value> {
        DictKey::from_value(key).and_then(|k| self.entries.remove(&k))
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }

    // ==================== Iteration ====================

    pub fn keys(&self) -> impl Iterator<Item = &DictKey> {
        self.entries.keys()
    }

    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.entries.values()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&DictKey, &Value)> {
        self.entries.iter()
    }

    // ==================== Transformation ====================

    pub fn merge(&self, other: &SimpleDict) -> SimpleDict {
        let mut result = self.entries.clone();
        for (k, v) in &other.entries {
            result.insert(k.clone(), v.clone());
        }
        SimpleDict { entries: result }
    }

    pub fn filter<F>(&self, predicate: F) -> SimpleDict
    where
        F: Fn(&DictKey, &Value) -> bool,
    {
        SimpleDict {
            entries: self.entries.iter()
                .filter(|(k, v)| predicate(k, v))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        }
    }

    pub fn map_values<F>(&self, f: F) -> SimpleDict
    where
        F: Fn(&Value) -> Value,
    {
        SimpleDict {
            entries: self.entries.iter()
                .map(|(k, v)| (k.clone(), f(v)))
                .collect(),
        }
    }
}

// Value helpers
impl Value {
    pub fn dict(entries: Vec<(Value, Value)>) -> Option<Value> {
        let mut dict = SimpleDict::new();
        for (k, v) in entries {
            let key = DictKey::from_value(&k)?;
            dict.insert(key, v);
        }
        Some(Value::Dict(Rc::new(RefCell::new(dict))))
    }

    pub fn empty_dict() -> Value {
        Value::Dict(Rc::new(RefCell::new(SimpleDict::new())))
    }
}
```

---

## Display Implementation

### Display Trait (value/display.rs)

```rust
// crates/runtime/src/value/display.rs

use super::*;
use std::fmt;

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(fl) => {
                if fl.fract() == 0.0 && fl.abs() < 1e15 {
                    write!(f, "{:.1}", fl)
                } else {
                    write!(f, "{}", fl)
                }
            }
            Value::Char(c) => write!(f, "{}", c),
            Value::String(s) => write!(f, "{}", s.as_str()),
            Value::Symbol(s) => write!(f, ":{}", s),
            Value::Tuple(t) => {
                write!(f, "(")?;
                for (i, v) in t.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
            Value::Array(arr) => {
                write!(f, "[")?;
                let arr = arr.borrow();
                for (i, v) in arr.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Dict(dict) => {
                write!(f, "{{")?;
                let dict = dict.borrow();
                for (i, (k, v)) in dict.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", k.to_value(), v)?;
                }
                write!(f, "}}")
            }
            Value::Struct(s) => {
                let s = s.borrow();
                write!(f, "{}(", s.type_name)?;
                for (i, (name, val)) in s.fields.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", name, val)?;
                }
                write!(f, ")")
            }
            Value::Enum(e) => {
                write!(f, "{}", e.variant)?;
                if !e.fields.is_empty() {
                    write!(f, "(")?;
                    for (i, v) in e.fields.iter().enumerate() {
                        if i > 0 { write!(f, ", ")?; }
                        write!(f, "{}", v)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Value::Function(func) => write!(f, "<fn {}>", func.name),
            Value::Closure(c) => write!(f, "<closure>"),
            Value::ActorRef(id) => write!(f, "<actor {}>", id.0),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s.as_str().escape_debug()),
            Value::Char(c) => write!(f, "'{}'", c.escape_debug()),
            _ => write!(f, "{}", self),
        }
    }
}
```

---

## Type Coercion

### Coercion Rules (types/coerce.rs)

```rust
// crates/runtime/src/types/coerce.rs

use crate::value::Value;

/// Coerce value for binary operations
pub fn coerce_binary(left: &Value, right: &Value) -> Option<(Value, Value)> {
    match (left, right) {
        // Same types - no coercion needed
        (Value::Int(_), Value::Int(_)) => Some((left.clone(), right.clone())),
        (Value::Float(_), Value::Float(_)) => Some((left.clone(), right.clone())),
        (Value::String(_), Value::String(_)) => Some((left.clone(), right.clone())),

        // Int + Float -> Float + Float
        (Value::Int(i), Value::Float(_)) => {
            Some((Value::Float(*i as f64), right.clone()))
        }
        (Value::Float(_), Value::Int(i)) => {
            Some((left.clone(), Value::Float(*i as f64)))
        }

        // String concatenation coercion
        (Value::String(_), other) => {
            let s = other.to_string();
            Some((left.clone(), Value::String(std::rc::Rc::new(
                crate::value::SimpleString::from_string(s)
            ))))
        }
        (other, Value::String(_)) => {
            let s = other.to_string();
            Some((Value::String(std::rc::Rc::new(
                crate::value::SimpleString::from_string(s)
            )), right.clone()))
        }

        _ => None,
    }
}

/// Coerce value for comparison
pub fn coerce_comparison(left: &Value, right: &Value) -> Option<std::cmp::Ordering> {
    match (left, right) {
        (Value::Int(a), Value::Int(b)) => Some(a.cmp(b)),
        (Value::Float(a), Value::Float(b)) => a.partial_cmp(b),
        (Value::Int(a), Value::Float(b)) => (*a as f64).partial_cmp(b),
        (Value::Float(a), Value::Int(b)) => a.partial_cmp(&(*b as f64)),
        (Value::String(a), Value::String(b)) => Some(a.as_str().cmp(b.as_str())),
        (Value::Char(a), Value::Char(b)) => Some(a.cmp(b)),
        _ => None,
    }
}

/// Check if value can be used as boolean
pub fn to_boolean(value: &Value) -> bool {
    !value.is_falsy()
}
```

---

## Cargo.toml

```toml
[package]
name = "simple-runtime"
version = "0.1.0"
edition = "2021"

[dependencies]
# No external dependencies for core types

[dev-dependencies]
criterion = "0.5"
```

---

## Summary

| Type | Representation | Mutable | Heap |
|------|----------------|---------|------|
| Nil | Unit variant | - | No |
| Bool | bool | - | No |
| Int | i64 | - | No |
| Float | f64 | - | No |
| Char | char | - | No |
| String | Rc<SimpleString> | No | Yes |
| Symbol | Rc<str> | No | Yes (interned) |
| Tuple | Rc<SimpleTuple> | No | Yes |
| Array | Rc<RefCell<SimpleArray>> | Yes | Yes |
| Dict | Rc<RefCell<SimpleDict>> | Yes | Yes |

All types implement Display for printing and support the basic operations needed by the Simple language runtime.
