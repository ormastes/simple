# Immutable Interface Design Research

## Overview

This document analyzes the design patterns for immutable interfaces in the Simple stdlib, comparing mutable vs immutable APIs and establishing guidelines for consistent immutable interface design.

## Current Implementation Analysis

### Mutable Pattern (core_nogc)

The `FixedVec` in `lib/std/core_nogc/fixed_vec.spl` represents the mutable API pattern:

```simple
# Mutates in-place, returns success indicator
pub fn push(self, value: T) -> bool:
    if self.len >= N:
        return false
    self.data[self.len] = value
    self.len = self.len + 1
    return true

# Mutates in-place, returns removed value
pub fn pop(self) -> Option[T]:
    if self.len == 0:
        return None
    self.len = self.len - 1
    return Some(self.data[self.len])
```

**Characteristics:**
- Methods mutate `self` in-place
- Return values indicate success/failure or return extracted data
- Efficient for single-threaded, performance-critical code
- Requires mutable references

### Immutable Pattern (core_nogc_immut)

The `StaticVec` in `lib/std/core_nogc_immut/static_vec.spl` represents the immutable API pattern:

```simple
# Returns new vector with element appended
fn push(self, val: T) -> Option[StaticVec[T, N]]:
    if self._len < N:
        var new_data = self._data
        new_data[self._len] = val
        Some(StaticVec { _data: new_data, _len: self._len + 1 })
    else:
        None

# Returns tuple of (extracted value, new vector)
fn pop(self) -> Option[(T, StaticVec[T, N])]:
    if self._len > 0:
        let val = self._data[self._len - 1]
        Some((val, StaticVec { _data: self._data, _len: self._len - 1 }))
    else:
        None
```

**Characteristics:**
- Methods return new instances instead of mutating
- Original value remains unchanged
- Enables structural sharing where applicable
- Thread-safe by default
- Better for functional programming style

### Persistent Pattern (core_immut)

The `List` in `lib/std/core_immut/persistent.spl` uses structural sharing:

```simple
enum List[T]:
    Nil
    Cons(T, Box[List[T]])

fn prepend(self, x: T) -> List[T]:
    List.Cons(x, Box.new(self))  # Reuses existing list
```

**Characteristics:**
- Efficient updates through structural sharing
- Garbage collector manages shared data
- O(1) prepend, O(n) append
- Best for functional algorithms

## Design Guidelines

### 1. Return Type Conventions

| Operation Type | Mutable Pattern | Immutable Pattern |
|----------------|-----------------|-------------------|
| Append/Insert | `fn push(self, v: T) -> bool` | `fn push(self, v: T) -> Option[Self]` |
| Remove/Pop | `fn pop(self) -> Option[T]` | `fn pop(self) -> Option[(T, Self)]` |
| Transform | `fn map(self, f: fn(T) -> T)` | `fn map(self, f: fn(T) -> U) -> Self` |
| Clear | `fn clear(self)` | `fn cleared() -> Self` |

### 2. Naming Conventions

For immutable modules, consider these naming patterns:

| Mutable Name | Immutable Name | Description |
|--------------|----------------|-------------|
| `push` | `push` / `with_pushed` | Returns new collection |
| `pop` | `pop` / `without_last` | Returns (value, new collection) |
| `set` | `with` / `updated` | Returns collection with updated value |
| `clear` | `cleared` / `empty` | Returns empty collection |
| `sort` | `sorted` | Returns sorted collection |

### 3. Self Parameter Conventions

```simple
# Mutable: takes &mut self or self (mutable)
pub fn push(self, value: T) -> bool

# Immutable: takes self (by value, consumes) or &self (borrows)
fn push(self, value: T) -> Option[StaticVec[T, N]]
```

### 4. Error Handling

```simple
# Mutable: returns bool or mutates + returns Result
pub fn try_push(self, value: T) -> Result[(), Error]

# Immutable: returns Option[NewType] or Result[NewType, Error]
fn push(self, val: T) -> Option[StaticVec[T, N]]
fn try_push(self, val: T) -> Result[StaticVec[T, N], Error]
```

## Variant Organization

### Module Naming

| Module | GC | Mutability | Use Case |
|--------|-----|------------|----------|
| `core` | any | mutable (default) | Core traits, Option, Result |
| `core_immut` | gc | immutable | Persistent data structures |
| `core_nogc` | no_gc | mutable | Stack-allocated collections |
| `core_nogc_immut` | no_gc | immutable | Immutable stack collections |

### Host Variants

| Variant | Concurrency | GC | Mutability |
|---------|-------------|-----|------------|
| `async_nogc_mut` | async | no_gc | mutable (DEFAULT) |
| `async_gc_mut` | async | gc | mutable |
| `async_gc_immut` | async | gc | immutable |
| `async_nogc_immut` | async | no_gc | immutable |
| `sync_nogc_mut` | sync | no_gc | mutable |
| `sync_gc_mut` | sync | gc | mutable |

## Immutable + GC Benefits

The `async_gc_immut` variant combines:

1. **Garbage Collection**: Automatic memory management, structural sharing
2. **Immutability**: Thread-safe by default, no race conditions
3. **Async**: Non-blocking I/O, efficient concurrency

**Ideal for:**
- Functional programming style
- Concurrent data processing
- Applications where safety > raw performance
- Scripts and rapid prototyping

## Implementation Recommendations

### 1. Trait-Based Abstraction

Define traits that both mutable and immutable types can implement:

```simple
trait Collection[T]:
    fn len(self) -> u64
    fn is_empty(self) -> bool
    fn get(self, idx: u64) -> Option[T]

trait MutableCollection[T]: Collection[T]:
    fn push(self, value: T) -> bool
    fn pop(self) -> Option[T]

trait ImmutableCollection[T]: Collection[T]:
    fn pushed(self, value: T) -> Option[Self]
    fn popped(self) -> Option[(T, Self)]
```

### 2. Builder Pattern for Immutable Types

```simple
struct VecBuilder[T]:
    items: FixedVec[T, 256]

impl VecBuilder[T]:
    fn new() -> VecBuilder[T]
    fn push(self, value: T) -> VecBuilder[T]
    fn build(self) -> PersistentVec[T]
```

### 3. Copy-on-Write for Hybrid APIs

```simple
struct CowVec[T]:
    inner: Shared[Vec[T]]

impl CowVec[T]:
    fn push(self, value: T) -> CowVec[T]:
        if self.inner.ref_count() == 1:
            # Unique reference, mutate in place
            self.inner.push(value)
            self
        else:
            # Shared reference, copy first
            let mut new_vec = self.inner.clone()
            new_vec.push(value)
            CowVec { inner: Shared.new(new_vec) }
```

## References

- [Types Specification](../spec/types.md) - Mutability rules for structs/classes
- [Stdlib Specification](../spec/stdlib.md) - Variant model
- [Concurrency Specification](../spec/concurrency.md) - Thread safety
