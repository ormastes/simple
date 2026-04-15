# Implementing Mutable Collections in Simple

**Date**: 2026-01-31
**Question**: How to implement `pop()` in Simple language itself (not Rust)?

---

## The Problem

Simple needs mutable collections (ArrayList, HashMap) where methods like `pop()` mutate in-place:

```simple
var arr = ArrayList.new([1, 2, 3])
val last = arr.pop()  # Should remove from arr and return 3
print(arr)            # Should print [1, 2]
```

But Simple is **value-based** - assignments create new values, not mutations.

---

## Solution: Class Field Mutation + FFI Primitives

### Strategy

1. **Rust FFI provides low-level primitives** (fast, unsafe operations)
2. **Simple classes wrap primitives** (safe, convenient API)
3. **Class fields are mutable with `me` keyword** (syntax sugar for reassignment)

---

## Implementation

### Step 1: Add Rust FFI Primitives

**File**: `rust/compiler/src/interpreter_extern/array_primitives.rs` (new)

```rust
/// Low-level array slice (returns new array without last element)
pub fn array_slice_to(args: &[Value]) -> Result<Value, CompileError> {
    let arr = eval_arg_array(args, 0)?;
    let end = eval_arg_int(args, 1)? as usize;

    if end > arr.len() {
        return Err(CompileError::semantic("slice end out of bounds"));
    }

    let sliced = arr[0..end].to_vec();
    Ok(Value::Array(sliced))
}

/// Low-level array concat (returns new array with elements appended)
pub fn array_concat(args: &[Value]) -> Result<Value, CompileError> {
    let arr1 = eval_arg_array(args, 0)?;
    let arr2 = eval_arg_array(args, 1)?;

    let mut result = arr1.to_vec();
    result.extend_from_slice(&arr2);
    Ok(Value::Array(result))
}

/// Low-level array get (returns element at index)
pub fn array_get(args: &[Value]) -> Result<Value, CompileError> {
    let arr = eval_arg_array(args, 0)?;
    let idx = eval_arg_int(args, 1)? as usize;

    arr.get(idx)
        .cloned()
        .ok_or_else(|| CompileError::semantic("index out of bounds"))
}

/// Low-level array length
pub fn array_len(args: &[Value]) -> Result<Value, CompileError> {
    let arr = eval_arg_array(args, 0)?;
    Ok(Value::Int(arr.len() as i64))
}
```

**Register in FFI dispatcher**:
```rust
// In interpreter_extern/mod.rs:
"array_slice_to" => array_primitives::array_slice_to(&evaluated),
"array_concat" => array_primitives::array_concat(&evaluated),
"array_get" => array_primitives::array_get(&evaluated),
"array_len" => array_primitives::array_len(&evaluated),
```

---

### Step 2: Implement ArrayList in Simple

**File**: `rust/lib/std/src/collections/array_list.spl` (new)

```simple
# Mutable array wrapper using class field mutation

export class ArrayList:
    items: [Value]  # Internal storage (immutable array)

    # Constructor
    static fn new(initial: [Value]) -> ArrayList:
        ArrayList(items: initial)

    # Create empty list
    static fn empty() -> ArrayList:
        ArrayList(items: [])

    # Get element at index
    fn get(index: i64) -> Value:
        array_get(self.items, index)

    # Get length
    fn len() -> i64:
        array_len(self.items)

    # Check if empty
    fn is_empty() -> bool:
        self.len() == 0

    # Pop last element (MUTABLE)
    me pop() -> Value:
        if self.is_empty():
            panic("pop from empty ArrayList")

        # Get last element
        val last_idx = self.len() - 1
        val last_elem = self.get(last_idx)

        # Create new array without last element
        self.items = array_slice_to(self.items, last_idx)

        # Return the removed element
        last_elem

    # Push element to end (MUTABLE)
    me push(value: Value):
        # Create new array with element appended
        self.items = array_concat(self.items, [value])

    # Insert at index (MUTABLE)
    me insert(index: i64, value: Value):
        if index < 0 or index > self.len():
            panic("insert index out of bounds")

        # Split array at index
        val before = array_slice_to(self.items, index)
        val after = array_slice_to(
            self.items,
            self.len()
        )[index:]  # Slice from index to end

        # Concatenate: before + [value] + after
        self.items = array_concat(
            array_concat(before, [value]),
            after
        )

    # Remove at index (MUTABLE)
    me remove(index: i64) -> Value:
        if index < 0 or index >= self.len():
            panic("remove index out of bounds")

        val elem = self.get(index)

        # Split and concatenate without element
        val before = array_slice_to(self.items, index)
        val after = array_slice_to(
            self.items,
            self.len()
        )[index + 1:]

        self.items = array_concat(before, after)
        elem

    # Clear all elements (MUTABLE)
    me clear():
        self.items = []

    # Iteration support
    fn iter() -> ArrayIterator:
        ArrayIterator.new(self.items)

    # Map (functional, returns new ArrayList)
    fn map(f: fn(Value) -> Value) -> ArrayList:
        val mapped = self.items.map(f)
        ArrayList.new(mapped)

    # Filter (functional, returns new ArrayList)
    fn filter(predicate: fn(Value) -> bool) -> ArrayList:
        val filtered = self.items.filter(predicate)
        ArrayList.new(filtered)
```

---

### Step 3: How Class Field Mutation Works

**Key insight**: `me` methods can reassign `self.field`:

```simple
class Container:
    value: i64

    me increment():
        self.value = self.value + 1  # ✅ Reassignment allowed in 'me' method

val c = Container(value: 10)
c.increment()  # Now c.value == 11
```

**Under the hood** (Rust implementation):
```rust
// When Simple code does: self.value = new_value
// Rust interpreter does:
match receiver {
    Value::Object { fields, .. } => {
        fields.insert("value".to_string(), new_value);  // Mutate HashMap
    }
}
```

So **class fields ARE mutable** (backed by HashMap in Rust), but **primitive arrays are not** (backed by Vec in Rust).

---

### Step 4: Why This Works

**ArrayList wraps an immutable array** but uses **reassignment** to simulate mutation:

```simple
me pop() -> Value:
    val last = self.get(self.len() - 1)

    # This line looks like mutation, but it's reassignment:
    self.items = array_slice_to(self.items, self.len() - 1)
    #            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    #            Creates NEW array, assigns to self.items

    last
```

**From the user's perspective**, it's mutation:
```simple
var list = ArrayList.new([1, 2, 3])
list.pop()  # Removes 3
print(list.items)  # [1, 2]
```

**Internally**, it's copy-on-write:
1. `array_slice_to()` creates new array `[1, 2]`
2. Assign new array to `self.items`
3. Old array `[1, 2, 3]` is garbage collected

---

## Performance Considerations

### Copy-on-Write Overhead

**Each mutation creates a new array**, which is O(n) instead of O(1):

```simple
# This is O(n²) instead of O(n):
var list = ArrayList.new([])
for i in 0..1000:
    list.push(i)  # Each push copies entire array
```

### Optimization: Persistent Data Structures

For better performance, implement **persistent vectors** (Clojure-style):

```simple
# Use a tree structure instead of flat array
class PersistentVector:
    root: Node
    tail: [Value]

    me push(value: Value):
        # Only copy tail (32 elements max), not entire tree
        # O(log₃₂ n) instead of O(n)
```

This is a **future optimization**, not needed initially.

---

## Alternative: True In-Place Mutation (Future)

If we want **true O(1) mutation**, add a `Ref<T>` type to Simple:

### Option A: Built-in Ref Type

```simple
# Add to Simple language:
class Ref<T>:
    # Internal: Backed by Rc<RefCell<T>> in Rust

    static fn new(value: T) -> Ref<T>:
        # FFI: Creates Rc::new(RefCell::new(value))

    fn get() -> T:
        # FFI: RefCell::borrow()

    me set(value: T):
        # FFI: RefCell::borrow_mut() + assign

# Usage:
class ArrayList:
    items: Ref<[Value]>

    me pop() -> Value:
        var arr = self.items.get()
        val last = arr[arr.len() - 1]
        arr = arr[0..arr.len()-1]
        self.items.set(arr)  # Still O(n), but clearer semantics
        last
```

### Option B: Add Mutable Array Primitive

```simple
# Add new Value variant in Rust:
pub enum Value {
    Array(Vec<Value>),           # Immutable
    MutableArray(Rc<RefCell<Vec<Value>>>),  # Mutable
}

# FFI primitive:
"mutable_array_new" => {
    let arr = eval_arg_array(args, 0)?;
    Ok(Value::MutableArray(Rc::new(RefCell::new(arr))))
}

"mutable_array_pop" => {
    let marr = eval_arg_mutable_array(args, 0)?;
    let mut arr_ref = marr.borrow_mut();
    arr_ref.pop().ok_or("empty array")?
}

# Simple code:
class ArrayList:
    items: MutableArray  # New primitive type

    static fn new(initial: [Value]) -> ArrayList:
        ArrayList(items: mutable_array_new(initial))

    me pop() -> Value:
        mutable_array_pop(self.items)  # O(1) mutation in Rust
```

---

## Recommendation

**For now**: Use **class field reassignment** (Step 2 above)
- ✅ Works with current Simple language (no new features)
- ✅ Simple to implement (just FFI primitives + Simple classes)
- ✅ Semantically clear (immutable arrays, mutable wrappers)
- ⚠️ O(n) performance (acceptable for most use cases)

**Future**: Add **Ref<T> type** or **MutableArray primitive**
- ✅ O(1) performance for mutations
- ❌ Requires language/runtime changes
- ❌ More complexity

---

## Implementation Plan for Decision #3

Update the plan to use **Simple stdlib** instead of Rust implementation:

### Phase 2.1: Mutable Collections in Simple (6-10h)

#### Step 1: Add Rust FFI Primitives (2-3h)
- `array_slice_to(arr, end)` - O(n) slice
- `array_concat(arr1, arr2)` - O(n) concatenation
- `array_get(arr, idx)` - O(1) indexing
- `array_len(arr)` - O(1) length
- Register in FFI dispatcher

#### Step 2: Implement ArrayList in Simple (2-3h)
- Create `rust/lib/std/src/collections/array_list.spl`
- Implement class with `items: [Value]` field
- Add `me pop()`, `me push()`, `me insert()`, etc.
- Use FFI primitives for operations

#### Step 3: Implement HashMap in Simple (1-2h)
- Create `rust/lib/std/src/collections/hash_map.spl`
- Use Simple dict as internal storage
- Add `me insert()`, `me remove()`, `me get()`, etc.

#### Step 4: Update Tests (1-2h)
- Change tests from `HashMap.new()` to `ArrayList.new()`
- Change tests from builtin array to ArrayList
- Verify mutations work correctly

**Total**: 6-10h, same as before
**Performance**: O(n) per mutation (acceptable for initial implementation)

---

## Example Usage

```simple
# User code:
use std.collections.ArrayList

var list = ArrayList.new([1, 2, 3])

list.push(4)
print(list.len())  # 4

val last = list.pop()
print(last)  # 4
print(list.len())  # 3

list.insert(1, 10)
print(list.items)  # [1, 10, 2, 3]

val removed = list.remove(2)
print(removed)  # 2
print(list.items)  # [1, 10, 3]

# Functional operations (immutable):
val doubled = list.map(\x: x * 2)
print(doubled.items)  # [2, 20, 6]
print(list.items)  # [1, 10, 3] (unchanged)
```

---

## Summary

**Answer**: Implement `pop()` in Simple using:
1. **Class field mutation** (`me` methods can reassign `self.items`)
2. **Rust FFI primitives** (array_slice_to, array_concat, etc.)
3. **Copy-on-write semantics** (create new array, reassign field)

**No RefCell needed in Simple** - it's hidden in the Rust implementation of class fields.

**Trade-off**: O(n) performance instead of O(1), but much simpler implementation.

**Future optimization**: Add Ref<T> type or MutableArray primitive for true O(1) mutations.
