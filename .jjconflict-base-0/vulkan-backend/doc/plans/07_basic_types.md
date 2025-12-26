# Basic Types Implementation Plan

## Index

| File | Content |
|------|---------|
| [07_basic_types.md](07_basic_types.md) | Part 1 |
| [07_basic_types_2.md](07_basic_types_2.md) | Part 2 |

---


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

---

Next: [Part 2](07_basic_types_2.md)
