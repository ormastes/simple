# Primitive as Object: C#-Style Type Promotion

This document describes how Simple promotes primitive syntax into rich object types, similar to C#'s unified type system where primitives are objects.

---

## Overview

Simple uses a **unified type model** where primitive-looking syntax automatically promotes to full object types:

| Syntax | Primitive Look | Object Type | Description |
|--------|---------------|-------------|-------------|
| `[]` | Array literal | `List[T]` | Dynamic, growable list |
| `[N]` | Fixed array | `Array[T, N]` | Fixed-size array |
| `str` | String literal | `String` | UTF-8 string object |
| `42` | Integer literal | `Int` | Integer object |
| `3.14` | Float literal | `Float` | Float object |
| `true`/`false` | Boolean literal | `Bool` | Boolean object |

This is similar to C# where `int` is an alias for `System.Int32`, `string` for `System.String`, etc.

---

## 1. Collection Type Promotion

### 1.1 `[]` → `List[T]` (Dynamic List)

The bracket syntax `[]` creates a `List[T]`, which is a dynamic, growable collection.

```simple
# Syntax
let items = [1, 2, 3]           # Type: List[i32]
let names = ["Alice", "Bob"]    # Type: List[String]
let empty: List[i32] = []       # Empty list

# Equivalent explicit form
let items = List.of(1, 2, 3)
let names = List.of("Alice", "Bob")
let empty = List[i32].new()
```

**List Characteristics:**

| Property | Value |
|----------|-------|
| Size | Dynamic (grows/shrinks) |
| Memory | Heap-allocated |
| Access | O(1) random access |
| Insert/Remove | O(n) middle, O(1) amortized end |
| Mutability | Mutable by default |

### 1.2 `[T; N]` → `Array[T, N]` (Fixed-Size Array)

The bracket syntax with size `[T; N]` creates an `Array[T, N]`, which is a fixed-size array.

```simple
# Syntax
let data: [i32; 10] = [0; 10]       # Type: Array[i32, 10], filled with zeros
let coords: [f64; 3] = [1.0, 2.0, 3.0]  # Type: Array[f64, 3]

# Equivalent explicit form
let data = Array[i32, 10].filled(0)
let coords = Array[f64, 3].of(1.0, 2.0, 3.0)

# Size must be compile-time constant
const SIZE = 100
let buffer: [u8; SIZE] = [0; SIZE]   # OK: SIZE is const

let n = get_size()
let bad: [u8; n] = ...               # ERROR: n is not const
```

**Array Characteristics:**

| Property | Value |
|----------|-------|
| Size | Fixed at compile time |
| Memory | Stack or heap (depending on context) |
| Access | O(1) random access |
| Insert/Remove | Not supported (fixed size) |
| Mutability | Mutable by default |

### 1.3 Comparison: List vs Array

| Feature | `List[T]` (`[]`) | `Array[T, N]` (`[T; N]`) |
|---------|------------------|--------------------------|
| Size | Dynamic | Fixed at compile time |
| Syntax | `[1, 2, 3]` | `[1, 2, 3]` (inferred) or `[i32; 3]` |
| Memory | Heap | Stack (small) or Heap (large) |
| Push/Pop | Yes | No |
| Resize | Yes | No |
| Use case | General collections | Fixed buffers, tuples, SIMD |
| No-GC safe | No (uses heap) | Yes (stack allocated) |
| Copy | Deep copy | Bitwise copy (if T: Copy) |

---

## 2. Immutable Collections

### 2.1 Immutable List → Linked List

When `#[immutable]` attribute is applied, `List[T]` is implemented as a **persistent linked list** for efficient structural sharing.

```simple
#[immutable]
let items = [1, 2, 3]           # Type: List[i32] (immutable, linked list)

# All operations return new lists
let more = items.appended(4)     # [1, 2, 3, 4] - new list, items unchanged
let head = items.head()          # Some(1)
let tail = items.tail()          # [2, 3] - structural sharing with items

# Efficient prepend (O(1))
let prepended = items.prepended(0)  # [0, 1, 2, 3]
```

**Immutable List (Linked List) Characteristics:**

| Property | Value |
|----------|-------|
| Size | Dynamic |
| Memory | Heap (nodes) |
| Prepend | O(1) |
| Append | O(n) or O(1) with finger tree variant |
| Random access | O(n) |
| Structural sharing | Yes |
| Thread-safe | Yes (immutable) |

**Implementation:**
```simple
# Internal structure (simplified)
struct ListNode[T]:
    value: T
    next: Option[*ListNode[T]]  # Shared pointer for structural sharing

struct List[T]:
    head: Option[*ListNode[T]]
    len: usize
```

### 2.2 Immutable Array → Copy-on-Write or New Copy

When `#[immutable]` is applied to fixed arrays, operations return new arrays:

```simple
#[immutable]
let coords: [f64; 3] = [1.0, 2.0, 3.0]

# All operations return new arrays
let updated = coords.with_index(0, 5.0)  # [5.0, 2.0, 3.0] - new array

# coords is unchanged
assert_eq(coords[0], 1.0)
```

---

## 3. String Type Promotion

### 3.1 `str` → `String` (String Object)

The `str` type is promoted to a full `String` object with rich methods.

```simple
# Syntax
let name: str = "Alice"         # Type: String
let greeting = "Hello, World!"  # Type: String

# Equivalent explicit form
let name = String.from("Alice")
let greeting = String.from("Hello, World!")

# String literals are always String objects
"hello".len()                   # 5
"hello".uppercased()            # "HELLO"
"hello".contains("ell")         # true
```

**String Characteristics:**

| Property | Value |
|----------|-------|
| Encoding | UTF-8 (always valid) |
| Memory | Heap-allocated, reference counted |
| Mutability | Mutable methods available |
| Immutable API | Available via `#[immutable]` |

### 3.2 `str` vs `String` Unification

Unlike Rust's `&str` vs `String` split, Simple uses a **single String type**:

```simple
# In Rust (confusing)
let s: &str = "hello";           # borrowed slice
let s: String = String::from("hello");  # owned

# In Simple (unified)
let s: str = "hello"             # Always String object
let s = "hello"                  # Same thing

# Functions accept str (which is String)
fn greet(name: str):             # Accepts String
    print("Hello, {name}")

greet("Alice")                   # OK
greet(some_string_var)           # OK
```

### 3.3 String vs Bytes

```simple
# Text (UTF-8, always valid)
let text: str = "hello"              # String object

# Binary data
let data: Bytes = Bytes.from([72, 101, 108, 108, 111])

# Conversion
let text = String.from_utf8(data)?   # May fail if invalid UTF-8
let data = text.as_bytes()           # Always succeeds
```

---

## 4. Array Unsafe/Danger Operations

### 4.1 Safe Default

By default, all array operations are bounds-checked:

```simple
let arr = [1, 2, 3]

arr[5]                          # Runtime panic: index out of bounds
arr.get(5)                      # Option[i32] = None (safe)
```

### 4.2 `danger` Block for Unsafe Operations

Use `danger` blocks (like Rust's `unsafe`) for unchecked access:

```simple
let arr = [1, 2, 3, 4, 5]

# Safe access
let value = arr.get(2).expect("index valid")

# Unchecked access (C-like) - must be in danger block
danger:
    let value = arr.get_unchecked(2)        # No bounds check
    arr.set_unchecked(2, 100)               # No bounds check
    let ptr = arr.as_ptr()                  # Raw pointer
    let value = ptr.offset(2).read()        # Pointer arithmetic

# Danger block required for:
# - get_unchecked / set_unchecked
# - Raw pointer operations
# - Unsafe memory access
```

### 4.3 Danger Operations List

| Operation | Safe Version | Danger Version |
|-----------|--------------|----------------|
| Index read | `arr.get(i)` → `Option[T]` | `arr.get_unchecked(i)` → `T` |
| Index write | `arr.set(i, v)` → `Result` | `arr.set_unchecked(i, v)` |
| Slice | `arr.slice(start, end)` | `arr.slice_unchecked(start, end)` |
| Raw pointer | N/A | `arr.as_ptr()` → `*T` |
| Mutable ptr | N/A | `arr.as_mut_ptr()` → `*mut T` |

### 4.4 Copy-on-Update (Immutable Context)

In immutable contexts, updates create new arrays:

```simple
#[immutable]
let arr = [1, 2, 3]

# These return new arrays (no danger needed)
let updated = arr.with_index(1, 100)      # [1, 100, 3] - new array
let appended = arr.appended(4)            # [1, 2, 3, 4] - for List only

# Original unchanged
assert_eq(arr, [1, 2, 3])
```

---

## 5. Numeric Type Promotion

### 5.1 Integer Literals → Int Object

```simple
# Integer literals are Int objects
let n = 42                      # Type: i64 (default)
let n: i32 = 42                 # Type: i32 (explicit)

# Methods available on literals
42.abs()                        # 42
(-5).is_negative()              # true
10.to_f64()                     # 10.0

# Ruby-style convenience
5.times(|i| print(i))           # 0, 1, 2, 3, 4
1.upto(5, |i| print(i))         # 1, 2, 3, 4, 5
```

### 5.2 Float Literals → Float Object

```simple
# Float literals are Float objects
let x = 3.14                    # Type: f64 (default)
let x: f32 = 3.14               # Type: f32 (explicit)

# Methods available on literals
3.14.floor()                    # 3.0
3.14.ceil()                     # 4.0
2.0.sqrt()                      # 1.414...
```

### 5.3 Boolean Literals → Bool Object

```simple
# Boolean literals are Bool objects
let flag = true                 # Type: Bool

# Methods
true.then_some(42)              # Some(42)
false.then_some(42)             # None
```

---

## 6. Type Aliases and Internal Representation

### 6.1 Primitive Syntax to Object Mapping

```simple
# These are equivalent (syntax sugar)
let a: []            # List[_]
let a: List[_]       # Same

let b: [T; N]        # Array[T, N]
let b: Array[T, N]   # Same

let c: str           # String
let c: String        # Same

let d: i32           # Int32
let d: Int32         # Same (but prefer i32)

let e: f64           # Float64
let e: Float64       # Same (but prefer f64)

let f: bool          # Bool
let f: Bool          # Same (but prefer bool)
```

### 6.2 Internal Implementation

The compiler maps primitive syntax to object types:

```simple
# Compiler transformation (conceptual)

# Source code
let items = [1, 2, 3]

# Lowered to
let items: List[i32] = List::of(1, 2, 3)

# Source code
let arr: [i32; 3] = [1, 2, 3]

# Lowered to
let arr: Array[i32, 3] = Array::of(1, 2, 3)
```

---

## 7. Shared Collection Traits

Both `List[T]` and `Array[T, N]` implement common traits, enabling generic programming over any sequence type (similar to C#'s `IList<T>`, `ICollection<T>`, `IEnumerable<T>`).

### 7.1 Trait Hierarchy

```
Iterable[T]                    # Can produce iterator
    │
    ├── Collection[T]          # Has length, can check containment
    │       │
    │       ├── Sequence[T]    # Indexed access (read)
    │       │       │
    │       │       ├── MutSequence[T]     # Indexed write
    │       │       │
    │       │       └── ImmutSequence[T]   # Functional updates
    │       │
    │       └── Growable[T]    # Can add/remove (List only)
    │
    └── Sliceable[T]           # Can create slices
```

### 7.2 Core Traits Definition

```simple
# ============================================
# Iterable - Base iteration trait
# ============================================

trait Iterable[T]:
    type Iter: Iterator[Item=T]

    fn iter(self) -> Self::Iter
    fn into_iter(self) -> Self::Iter

# ============================================
# Collection - Sized container
# ============================================

trait Collection[T]: Iterable[T]:
    fn len(self) -> usize

    fn is_empty(self) -> bool:
        self.len() == 0

    fn contains(self, item: &T) -> bool where T: Eq:
        for x in self.iter():
            if x.eq(item):
                return true
        false

# ============================================
# Sequence - Indexed read access
# ============================================

trait Sequence[T]: Collection[T]:
    # Safe indexed access
    fn get(self, idx: usize) -> Option[T]

    # First/last element
    fn first(self) -> Option[T]:
        self.get(0)

    fn last(self) -> Option[T]:
        if self.is_empty():
            None
        else:
            self.get(self.len() - 1)

    # Search
    fn find(self, predicate: fn(&T) -> bool) -> Option[T]:
        for item in self.iter():
            if predicate(&item):
                return Some(item)
        None

    fn find_index(self, predicate: fn(&T) -> bool) -> Option[usize]:
        for (idx, item) in self.iter().enumerate():
            if predicate(&item):
                return Some(idx)
        None

    fn position(self, item: &T) -> Option[usize] where T: Eq:
        self.find_index(|x| x.eq(item))

    # Slicing
    fn slice(self, range: Range[usize]) -> Slice[T]

    # Iteration with index
    fn enumerate(self) -> Enumerate[Self::Iter]:
        self.iter().enumerate()

# ============================================
# MutSequence - Mutable indexed access
# ============================================

trait MutSequence[T]: Sequence[T]:
    # Mutable access
    fn get_mut(self, idx: usize) -> Option[&mut T]

    # Set value at index
    fn set(self, idx: usize, value: T) -> Result[(), IndexError]

    # Swap two elements
    fn swap(self, i: usize, j: usize):
        if i != j:
            let tmp = self.get(i).expect("valid index")
            self.set(i, self.get(j).expect("valid index"))
            self.set(j, tmp)

    # Fill all elements
    fn fill(self, value: T) where T: Clone:
        for i in 0..self.len():
            self.set(i, value.clone())

    # In-place sort
    fn sort(self) where T: Ord

    # In-place reverse
    fn reverse(self)

    # In-place filter (mutable only for List)
    fn retain(self, predicate: fn(&T) -> bool)

# ============================================
# ImmutSequence - Functional update operations
# ============================================

trait ImmutSequence[T]: Sequence[T]:
    type Output: Sequence[T]

    # Return new sequence with updated index
    fn with_index(self, idx: usize, value: T) -> Self::Output

    # Return new sorted sequence
    fn sorted(self) -> Self::Output where T: Ord

    # Return new reversed sequence
    fn reversed(self) -> Self::Output

    # Return new filtered sequence
    fn filtered(self, predicate: fn(&T) -> bool) -> Self::Output

    # Return new mapped sequence
    fn mapped[U](self, f: fn(T) -> U) -> Self::Output

# ============================================
# Growable - Can add/remove elements
# ============================================

trait Growable[T]: MutSequence[T]:
    # Add to end
    fn push(self, item: T)

    # Remove from end
    fn pop(self) -> Option[T]

    # Add to front
    fn push_front(self, item: T)

    # Remove from front
    fn pop_front(self) -> Option[T]

    # Insert at index
    fn insert(self, idx: usize, item: T) -> Result[(), IndexError]

    # Remove at index
    fn remove(self, idx: usize) -> Option[T]

    # Remove all elements
    fn clear(self)

    # Extend with iterator
    fn extend[I: IntoIterator[Item=T]](self, iter: I)

    # Append another collection
    fn append(self, other: Self)

# ============================================
# Sliceable - Can create slice views
# ============================================

trait Sliceable[T]:
    fn as_slice(self) -> Slice[T]
    fn as_mut_slice(self) -> MutSlice[T]
```

### 7.3 Trait Implementations

```simple
# List implements all mutable traits
impl Iterable[T] for List[T]
impl Collection[T] for List[T]
impl Sequence[T] for List[T]
impl MutSequence[T] for List[T]
impl ImmutSequence[T] for List[T]
impl Growable[T] for List[T]
impl Sliceable[T] for List[T]

# Array implements fixed-size traits
impl Iterable[T] for Array[T, N]
impl Collection[T] for Array[T, N]
impl Sequence[T] for Array[T, N]
impl MutSequence[T] for Array[T, N]
impl ImmutSequence[T] for Array[T, N]
impl Sliceable[T] for Array[T, N]
# Note: Array does NOT implement Growable (fixed size)

# Slice implements read-only traits
impl Iterable[T] for Slice[T]
impl Collection[T] for Slice[T]
impl Sequence[T] for Slice[T]
# Slice is borrowed, no ownership for mutation

# String implements sequence traits for chars
impl Iterable[char] for String
impl Collection[char] for String
impl Sequence[char] for String
impl ImmutSequence[char] for String
```

### 7.4 Generic Functions Over Collections

With shared traits, you can write generic functions:

```simple
# Works with List, Array, Slice, String
fn sum[C: Sequence[T], T: Add[Output=T] + Default](seq: C) -> T:
    var total = T::default()
    for item in seq.iter():
        total = total + item
    total

# Works with List and Array
fn find_max[C: Sequence[T], T: Ord](seq: C) -> Option[T]:
    if seq.is_empty():
        return None
    var max = seq.first().expect("not empty")
    for item in seq.iter():
        if item.gt(&max):
            max = item
    Some(max)

# Works with any mutable sequence
fn reverse_in_place[C: MutSequence[T], T](seq: &mut C):
    var left: usize = 0
    var right = seq.len() - 1
    while left < right:
        seq.swap(left, right)
        left = left + 1
        right = right - 1

# Works with any growable collection
fn deduplicate[C: Growable[T], T: Eq](seq: &mut C):
    var seen = Set[T].new()
    seq.retain(|item|
        if seen.contains(item):
            false
        else:
            seen.insert(item.clone())
            true
    )
```

### 7.5 Usage Examples

```simple
# Generic function accepts both List and Array
fn print_all[C: Sequence[T], T: Display](items: C):
    for item in items.iter():
        print(item)

let list = [1, 2, 3]              # List[i32]
let array: [i32; 3] = [4, 5, 6]   # Array[i32, 3]

print_all(list)                    # Works
print_all(array)                   # Works

# Type constraint ensures only sequences with get()
fn safe_middle[C: Sequence[T], T](seq: C) -> Option[T]:
    let mid = seq.len() / 2
    seq.get(mid)

# Only List (Growable) can use push
fn append_all[C: Growable[T], T](dest: &mut C, items: &[T]) where T: Clone:
    for item in items:
        dest.push(item.clone())
```

### 7.6 Trait Summary Table

| Trait | List | Array | Slice | String | Description |
|-------|------|-------|-------|--------|-------------|
| `Iterable[T]` | ✓ | ✓ | ✓ | ✓ | Can iterate |
| `Collection[T]` | ✓ | ✓ | ✓ | ✓ | Has len, contains |
| `Sequence[T]` | ✓ | ✓ | ✓ | ✓ | Indexed read |
| `MutSequence[T]` | ✓ | ✓ | ✗ | ✗ | Indexed write |
| `ImmutSequence[T]` | ✓ | ✓ | ✗ | ✓ | Functional updates |
| `Growable[T]` | ✓ | ✗ | ✗ | ✗ | Add/remove |
| `Sliceable[T]` | ✓ | ✓ | ✓ | ✓ | Create slices |

---

## 8. Collection Object APIs

### 8.1 List[T] API (Dynamic)

```simple
impl List[T]:
    # Constructors
    fn new() -> List[T]
    fn of(items: T...) -> List[T]
    fn with_capacity(cap: usize) -> List[T]
    fn filled(value: T, count: usize) -> List[T]
    fn from_iter[I: Iterator[Item=T]](iter: I) -> List[T]

    # Size
    fn len(self) -> usize
    fn is_empty(self) -> bool
    fn capacity(self) -> usize

    # Access (safe)
    fn get(self, idx: usize) -> Option[T]
    fn first(self) -> Option[T]
    fn last(self) -> Option[T]

    # Mutation (mutable context)
    fn push(self, item: T)
    fn pop(self) -> Option[T]
    fn insert(self, idx: usize, item: T)
    fn remove(self, idx: usize) -> Option[T]
    fn clear(self)

    # Immutable operations (return new)
    fn appended(self, item: T) -> List[T]
    fn prepended(self, item: T) -> List[T]
    fn with_index(self, idx: usize, value: T) -> List[T]
    fn filtered(self, predicate: fn(&T) -> bool) -> List[T]
    fn mapped[U](self, f: fn(T) -> U) -> List[U]
    fn sorted(self) -> List[T] where T: Ord
    fn reversed(self) -> List[T]

    # Iteration
    fn iter(self) -> Iterator[Item=&T]
    fn iter_mut(self) -> Iterator[Item=&mut T]
    fn into_iter(self) -> Iterator[Item=T]

    # Slicing
    fn slice(self, range: Range) -> Slice[T]
    fn as_slice(self) -> Slice[T]
```

### 8.2 Array[T, N] API (Fixed)

```simple
impl Array[T, const N: usize]:
    # Implements: Iterable, Collection, Sequence, MutSequence, ImmutSequence, Sliceable
    # Does NOT implement: Growable (fixed size)

    # Constructors
    fn new() -> Array[T, N] where T: Default
    fn of(items: T...) -> Array[T, N]    # N items required
    fn filled(value: T) -> Array[T, N]
    fn filled_with(f: fn(usize) -> T) -> Array[T, N]

    # From Collection trait (compile-time known)
    fn len(self) -> usize { N }
    fn is_empty(self) -> bool { N == 0 }
    fn contains(self, item: &T) -> bool where T: Eq

    # From Sequence trait
    fn get(self, idx: usize) -> Option[T]
    fn first(self) -> Option[T]
    fn last(self) -> Option[T]
    fn find(self, predicate: fn(&T) -> bool) -> Option[T]
    fn find_index(self, predicate: fn(&T) -> bool) -> Option[usize]
    fn position(self, item: &T) -> Option[usize] where T: Eq

    # From MutSequence trait
    fn get_mut(self, idx: usize) -> Option[&mut T]
    fn set(self, idx: usize, value: T) -> Result[(), IndexError]
    fn swap(self, i: usize, j: usize)
    fn fill(self, value: T) where T: Clone
    fn sort(self) where T: Ord
    fn reverse(self)

    # From ImmutSequence trait
    fn with_index(self, idx: usize, value: T) -> Array[T, N]
    fn sorted(self) -> Array[T, N] where T: Ord
    fn reversed(self) -> Array[T, N]
    fn filtered(self, predicate: fn(&T) -> bool) -> List[T]  # Returns List (size unknown)
    fn mapped[U](self, f: fn(T) -> U) -> Array[U, N]

    # From Iterable trait
    fn iter(self) -> ArrayIter[T, N]
    fn iter_mut(self) -> ArrayIterMut[T, N]
    fn into_iter(self) -> ArrayIntoIter[T, N]

    # From Sliceable trait
    fn slice(self, range: Range) -> Slice[T]
    fn as_slice(self) -> Slice[T]
    fn as_mut_slice(self) -> MutSlice[T]

    # Danger operations (require danger block)
    danger fn get_unchecked(self, idx: usize) -> T
    danger fn set_unchecked(self, idx: usize, value: T)
    danger fn as_ptr(self) -> *T
    danger fn as_mut_ptr(self) -> *mut T

    # Conversion
    fn to_list(self) -> List[T]
```

### 8.3 String API

```simple
impl String:
    # Constructors
    fn new() -> String
    fn from(s: &str) -> String
    fn from_utf8(bytes: Bytes) -> Result[String, Utf8Error]
    fn from_utf8_lossy(bytes: Bytes) -> String
    fn with_capacity(cap: usize) -> String

    # Size
    fn len(self) -> usize                  # Byte length
    fn char_count(self) -> usize           # Character count
    fn is_empty(self) -> bool

    # Access
    fn get(self, idx: usize) -> Option[char]
    fn byte_at(self, idx: usize) -> Option[u8]
    fn char_at(self, idx: usize) -> Option[char]

    # Search
    fn contains(self, sub: &str) -> bool
    fn starts_with(self, prefix: &str) -> bool
    fn ends_with(self, suffix: &str) -> bool
    fn find(self, sub: &str) -> Option[usize]

    # Transformation (return new strings)
    fn trimmed(self) -> String
    fn uppercased(self) -> String
    fn lowercased(self) -> String
    fn replaced(self, old: &str, new: &str) -> String
    fn split(self, sep: &str) -> Iterator[String]

    # Mutation (mutable context)
    fn push(self, c: char)
    fn push_str(self, s: &str)
    fn pop(self) -> Option[char]
    fn clear(self)

    # Conversion
    fn as_bytes(self) -> &[u8]
    fn to_bytes(self) -> Bytes
    fn chars(self) -> Iterator[char]
```

---

## 9. Summary

### 9.1 Type Mapping Table

| Primitive Syntax | Object Type | Mutable Impl | Immutable Impl |
|------------------|-------------|--------------|----------------|
| `[]` | `List[T]` | Vec-like (heap, growable) | Linked list (structural sharing) |
| `[T; N]` | `Array[T, N]` | Fixed buffer | Copy-on-write / new copy |
| `str` / `"..."` | `String` | Mutable string buffer | Immutable string |
| `i8`-`i64` | `Int8`-`Int64` | N/A (value type) | N/A (value type) |
| `f32`/`f64` | `Float32`/`Float64` | N/A (value type) | N/A (value type) |
| `bool` | `Bool` | N/A (value type) | N/A (value type) |

### 9.2 Shared Traits Summary

| Trait | Purpose | List | Array | Slice | String |
|-------|---------|------|-------|-------|--------|
| `Iterable[T]` | Iteration | ✓ | ✓ | ✓ | ✓ |
| `Collection[T]` | len, contains | ✓ | ✓ | ✓ | ✓ |
| `Sequence[T]` | Indexed read | ✓ | ✓ | ✓ | ✓ |
| `MutSequence[T]` | Indexed write | ✓ | ✓ | ✗ | ✗ |
| `ImmutSequence[T]` | Functional ops | ✓ | ✓ | ✗ | ✓ |
| `Growable[T]` | Add/remove | ✓ | ✗ | ✗ | ✗ |
| `Sliceable[T]` | Create slices | ✓ | ✓ | ✓ | ✓ |

### 9.3 Design Principles

1. **Unified type model** - Primitives are objects (like C#)
2. **Safe by default** - Bounds checking, no null
3. **Explicit unsafety** - `danger` blocks for unchecked operations
4. **Immutable-friendly** - Structural sharing for immutable collections
5. **No String/str confusion** - Single string type
6. **No implicit conversions** - Explicit `.to_*()` methods
7. **Shared interfaces** - Generic programming via common traits

### 9.4 When to Use Each

| Use Case | Recommended Type | Key Trait |
|----------|-----------------|-----------|
| General collections | `List[T]` (`[]`) | `Growable` |
| Fixed-size buffers | `Array[T, N]` (`[T; N]`) | `MutSequence` |
| SIMD/GPU data | `Array[T, N]` (stack, no GC) | `Sequence` |
| No-GC contexts | `Array[T, N]` (stack) | `Sequence` |
| Functional programming | `List[T]` with `#[immutable]` | `ImmutSequence` |
| Generic algorithms | Accept `Sequence[T]` | `Sequence` |
| Text processing | `String` (`str`) | `ImmutSequence` |
| Binary data | `Bytes` | `Sequence` |
| Performance-critical loops | `danger` + unchecked access | N/A |

---

## Related Specifications

- [Types and Mutability](types.md)
- [Traits](traits.md)
- [Data Structures](data_structures.md)
- [Memory and Ownership](memory.md)
- [Standard Library](stdlib.md)
