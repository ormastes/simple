# Customizing Backend Types for `[]` and `{}` Literals

**Date**: 2026-01-31
**Question**: "[], {} can change backend type by __init__?"

---

## The Question

Can we customize what backend type gets created when using array/dict literal syntax?

**Example**:
```simple
val arr = [1, 2, 3]  # Creates Array by default

# But can we make it create ArrayList instead?
val arr: ArrayList = [1, 2, 3]  # Uses ArrayList backend

# Or even custom types?
val arr: MyCustomList = [1, 2, 3]  # Uses user-defined backend
```

**Answer: YES!** We can support this with several approaches.

---

## Option 1: Type Inference with `from()` Conversion ⭐ RECOMMENDED

### Design

**Type annotation triggers conversion**:

```simple
# Default: Creates built-in Array
val arr = [1, 2, 3]  # Type: Array<i64>, Backend: Rc<RefCell<Vec<Value>>>

# Type annotation: Converts to ArrayList
val arr: ArrayList = [1, 2, 3]  # Type: ArrayList, Backend: custom

# Type annotation: Converts to Vector
val arr: Vector<i64> = [1, 2, 3]  # Type: Vector, Backend: custom
```

### Implementation

**Classes define `from()` static method**:

```simple
class ArrayList:
    items: [Value]

    # Called when converting from array literal
    static fn from(data: [Value]) -> ArrayList:
        ArrayList(items: data)

    me push(value: Value):
        self.items = self.items + [value]  # Uses built-in array internally

    me pop() -> Value:
        val last = self.items[self.items.len() - 1]
        self.items = self.items[0..self.items.len() - 1]
        last

# Usage:
val arr: ArrayList = [1, 2, 3]  # Calls ArrayList.from([1, 2, 3])
```

**Compiler transformation**:
```simple
val arr: ArrayList = [1, 2, 3]

# Compiles to:
val arr = ArrayList.from([1, 2, 3])
```

### Pros
- ✅ Clean syntax (just add type annotation)
- ✅ Explicit conversion (no magic)
- ✅ Works with any type that implements `from()`
- ✅ Familiar pattern (Rust's `From` trait)

### Cons
- ⚠️ Requires type annotation (can't infer from usage)

---

## Option 2: Magic `__from_array__` Method

### Design

**Classes implement special `__from_array__` to customize literal construction**:

```simple
class ArrayList:
    items: [Value]

    # Special method called when constructing from array literal
    static fn __from_array__(data: [Value]) -> ArrayList:
        print("Creating ArrayList from literal")
        ArrayList(items: data)

# Usage:
val arr: ArrayList = [1, 2, 3]  # Calls ArrayList.__from_array__([1, 2, 3])
```

**Similarly for dicts**:
```simple
class HashMap:
    buckets: [[KeyValue]]

    static fn __from_dict__(data: {text: Value}) -> HashMap:
        val hm = HashMap(buckets: [[], [], [], []])
        for key, value in data:
            hm.insert(key, value)
        hm

# Usage:
val map: HashMap = {"a": 1, "b": 2}  # Calls HashMap.__from_dict__({...})
```

### Implementation

**Compiler checks for `__from_array__` when type is specified**:

```rust
// In interpreter_call/mod.rs:
Expr::ArrayLiteral { elements } => {
    let values = evaluate_elements(elements)?;

    // Check if target type has __from_array__
    if let Some(target_type) = expected_type {
        if let Some(class) = classes.get(&target_type.name()) {
            if let Some(from_array_method) = class.static_methods.get("__from_array__") {
                // Call __from_array__(values)
                return call_static_method(class, "__from_array__", vec![Value::Array(values)])?;
            }
        }
    }

    // Default: create built-in Array
    Ok(Value::Array(Rc::new(RefCell::new(values))))
}
```

### Pros
- ✅ Clean user syntax
- ✅ Full control over construction
- ✅ Can add custom initialization logic

### Cons
- ⚠️ Magic method (less explicit than `from()`)
- ⚠️ Requires type annotation

---

## Option 3: Implicit Type from Context (Advanced)

### Design

**Infer type from usage, not just annotation**:

```simple
# No type annotation, but ArrayList has push method:
val arr = [1, 2, 3]
arr.push(4)  # Compiler infers: "push() exists on ArrayList, not Array, so upgrade to ArrayList"

# Or based on function parameter:
fn process_list(data: ArrayList):
    data.push(10)

process_list([1, 2, 3])  # Infers ArrayList from parameter type
```

### Implementation

**Two-pass compilation**:
1. **First pass**: Create generic array literal
2. **Second pass**: Analyze usage and convert if needed

```rust
// First pass:
val arr = [1, 2, 3]  // Type: Array (default)

// Second pass (usage analysis):
arr.push(4)  // push() requires ArrayList
// -> Insert conversion: val arr = ArrayList.from([1, 2, 3])
```

### Pros
- ✅ No type annotations needed
- ✅ Smart inference based on usage
- ✅ Feels like dynamic typing

### Cons
- ❌ Very complex to implement (requires flow analysis)
- ❌ Can be confusing (implicit conversions)
- ❌ Error messages harder to understand

---

## Option 4: Default Backend + Explicit Conversion

### Design

**`[]` and `{}` always create default types, use explicit constructors for custom types**:

```simple
# Default: Built-in array
val arr = [1, 2, 3]  # Always creates Array<i64>

# Custom: Explicit constructor
val list = ArrayList.new([1, 2, 3])  # Creates ArrayList
val vec = Vector.from([1, 2, 3])     # Creates Vector

# Or with type annotation + from():
val list: ArrayList = [1, 2, 3]  # Calls ArrayList.from()
```

### Pros
- ✅ Simple and explicit
- ✅ No magic behavior
- ✅ Easy to understand

### Cons
- ⚠️ Slightly more verbose for custom types
- ⚠️ Two ways to do the same thing

---

## Comparison

| Option | Syntax | Type Annotation Required? | Magic? | Complexity | Explicitness |
|--------|--------|---------------------------|--------|------------|--------------|
| **1. from()** | `val arr: T = [...]` | Yes | No | Low | High |
| **2. __from_array__** | `val arr: T = [...]` | Yes | Yes | Medium | Medium |
| **3. Context inference** | `val arr = [...]` | No | Yes | **Very High** | Low |
| **4. Explicit constructor** | `val arr = T.new([...])` | No | No | Low | Very High |

---

## Recommendation: Option 1 + Option 4 (Hybrid)

**Combine `from()` conversion with explicit constructors**:

### Default Behavior (No Type Annotation)

```simple
val arr = [1, 2, 3]  # Creates built-in Array (mutable by default)
val dict = {"a": 1}   # Creates built-in Dict (mutable by default)
```

### Type Annotation Conversion

```simple
val arr: ArrayList = [1, 2, 3]  # Calls ArrayList.from([1, 2, 3])
val vec: Vector<i64> = [1, 2, 3]  # Calls Vector.from([1, 2, 3])
```

### Explicit Constructor (Alternative)

```simple
val arr = ArrayList.new([1, 2, 3])  # Direct construction
val vec = Vector.from_slice([1, 2, 3])  # Named constructor
```

### Implementation

**1. Built-in types remain simple**:
```rust
// [] always creates Array
Expr::ArrayLiteral { elements } => {
    let values = evaluate_elements(elements)?;
    Ok(Value::Array(Rc::new(RefCell::new(values))))
}
```

**2. Type annotation triggers from() call**:
```rust
// Check if expected type differs from default
if let Some(expected_type) = expected_type {
    if expected_type != Type::Array {
        // Call TargetType.from(array)
        return call_static_method(expected_type, "from", vec![array_value])?;
    }
}
```

**3. Classes implement from()**:
```simple
# Standard library: ArrayList
export class ArrayList:
    items: [Value]

    static fn from(data: [Value]) -> ArrayList:
        ArrayList(items: data)

    static fn new(data: [Value]) -> ArrayList:
        ArrayList.from(data)  # Alias for convenience

# User code:
val arr: ArrayList = [1, 2, 3]  # Uses from()
val arr2 = ArrayList.new([1, 2, 3])  # Uses new()
```

---

## Examples

### Example 1: ArrayList with Custom Backend

```simple
# Define ArrayList with optimized backend
export class ArrayList:
    # Backend: Uses chunked storage for better performance
    chunks: [[Value]]
    size: i64

    static fn from(data: [Value]) -> ArrayList:
        # Chunk data into 32-element blocks
        val chunks = []
        for i in 0..data.len() by 32:
            chunks.push(data[i..min(i+32, data.len())])

        ArrayList(chunks: chunks, size: data.len())

    fn get(index: i64) -> Value:
        val chunk_idx = index / 32
        val elem_idx = index % 32
        self.chunks[chunk_idx][elem_idx]

    me push(value: Value):
        # Add to last chunk or create new chunk
        if self.chunks[-1].len() < 32:
            self.chunks[-1].push(value)
        else:
            self.chunks.push([value])
        self.size += 1

# Usage:
val arr: ArrayList = [1, 2, 3, 4, 5]  # Uses chunked backend
arr.push(6)  # O(1) operation
```

### Example 2: HashMap with Custom Backend

```simple
export class HashMap:
    buckets: [[KeyValue]]
    count: i64

    static fn from(data: {text: Value}) -> HashMap:
        val hm = HashMap(buckets: [[] for _ in 0..16], count: 0)
        for key, value in data:
            hm.insert(key, value)
        hm

    me insert(key: text, value: Value):
        val hash = key.hash() % self.buckets.len()
        self.buckets[hash].push(KeyValue(key: key, value: value))
        self.count += 1

# Usage:
val map: HashMap = {"a": 1, "b": 2}  # Uses hash table backend
map.insert("c", 3)  # O(1) expected
```

### Example 3: Persistent Vector (Immutable)

```simple
export class PersistentVector:
    root: Node
    tail: [Value]

    static fn from(data: [Value]) -> PersistentVector:
        # Build tree structure for O(log n) operations
        val pv = PersistentVector.empty()
        for elem in data:
            pv = pv.push(elem)  # Returns new vector (immutable)
        pv

    fn push(value: Value) -> PersistentVector:
        # Returns new vector with element added (structural sharing)
        # O(log32 n) complexity
        # ...

# Usage:
val vec: PersistentVector = [1, 2, 3]  # Builds tree structure
val vec2 = vec.push(4)  # Creates new vector, shares structure with vec
```

---

## Type System Integration

### Coercion Rules

```simple
# Arrays can coerce to ArrayList:
fn process(data: ArrayList):
    data.push(10)

process([1, 2, 3])  # OK: [1, 2, 3] coerces to ArrayList via from()

# But not vice versa (unless ArrayList implements to_array()):
fn process_array(data: [i64]):
    # ...

val arr = ArrayList.new([1, 2, 3])
process_array(arr)  # ERROR: ArrayList is not [i64]
process_array(arr.to_array())  # OK: explicit conversion
```

### Type Annotations

```simple
# Function parameters can specify custom types:
fn filter(data: ArrayList, predicate: fn(Value) -> bool) -> ArrayList:
    val result = ArrayList.new([])
    for item in data:
        if predicate(item):
            result.push(item)
    result

# Call with literal:
val evens = filter([1, 2, 3, 4, 5, 6], \x: x % 2 == 0)
# Literal [1, 2, 3, 4, 5, 6] coerces to ArrayList
```

---

## Implementation Plan

### Step 1: Add `from()` Support to Type System (3-4h)

**File**: `rust/compiler/src/hir/type_inference.rs`

```rust
// When type annotation exists and differs from literal type:
pub fn apply_type_coercion(
    value: Value,
    target_type: &Type,
    classes: &HashMap<String, Class>,
) -> Result<Value, CompileError> {
    match (value, target_type) {
        (Value::Array(arr), Type::Class(class_name)) => {
            // Check if class has from() static method
            if let Some(class) = classes.get(class_name) {
                if let Some(_) = class.static_methods.get("from") {
                    // Call ClassName.from(arr)
                    return call_static_method(class_name, "from", vec![Value::Array(arr)])?;
                }
            }
            Err(CompileError::type_error(format!(
                "cannot convert Array to {} (no from() method)",
                class_name
            )))
        }
        _ => Ok(value),  // No coercion needed
    }
}
```

### Step 2: Implement Standard Library Collections (4-6h)

**File**: `rust/lib/std/src/collections/array_list.spl`

```simple
export class ArrayList:
    items: [Value]

    static fn from(data: [Value]) -> ArrayList:
        ArrayList(items: data)

    static fn new(data: [Value]) -> ArrayList:
        ArrayList.from(data)

    fn len() -> i64:
        self.items.len()

    fn get(index: i64) -> Value:
        self.items[index]

    me push(value: Value):
        self.items = self.items + [value]

    me pop() -> Value:
        val last = self.items[self.items.len() - 1]
        self.items = self.items[0..self.items.len() - 1]
        last
```

**File**: `rust/lib/std/src/collections/hash_map.spl`

```simple
export class HashMap:
    pairs: [{text: Value}]

    static fn from(data: {text: Value}) -> HashMap:
        HashMap(pairs: [data])

    me insert(key: text, value: Value):
        self.pairs[0][key] = value

    fn get(key: text) -> Option<Value>:
        self.pairs[0].get(key)
```

### Step 3: Testing (1-2h)

```simple
# test/system/features/literal_conversion_spec.spl

describe "literal to custom type conversion":
    it "should convert array to ArrayList":
        val arr: ArrayList = [1, 2, 3]
        expect(arr.len()).to_equal(3)

    it "should convert dict to HashMap":
        val map: HashMap = {"a": 1, "b": 2}
        expect(map.get("a")).to_equal(Some(1))

    it "should work in function parameters":
        fn process(data: ArrayList):
            data.len()

        val len = process([1, 2, 3])  # Array coerces to ArrayList
        expect(len).to_equal(3)
```

**Total effort**: 8-12h

---

## Answer to Your Question

**Yes, `[]` and `{}` can use different backend types!**

**How**:
1. **Type annotation**: `val arr: ArrayList = [1, 2, 3]`
2. **Calls `from()` method**: `ArrayList.from([1, 2, 3])`
3. **Custom backend**: ArrayList can use any internal representation

**Example backends**:
- `ArrayList`: Chunked storage
- `Vector`: Contiguous memory
- `PersistentVector`: Tree structure (immutable)
- `HashMap`: Hash table
- `TreeMap`: Red-black tree

**Default behavior**:
- `[]` → `Array` (mutable, RefCell-backed)
- `{}` → `Dict` (mutable, HashMap-backed)

**Custom types**: Add type annotation and implement `from()` static method.
