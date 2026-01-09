# Basic Types Implementation Plan - Part 2

Part of [Basic Types Plan](07_basic_types.md).

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
---

Back to: [Part 1](07_basic_types.md)
