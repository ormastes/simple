# `val` vs `var` with `mut` Collections - Semantics

**Date**: 2026-01-31
**Question**: "is 'val = mut[..]' possible in concept?"

---

## The Question

Is this valid and useful?

```simple
val arr = mut [1, 2, 3]  # val (immutable binding) + mut (mutable collection)
```

**Answer: YES!** This is conceptually valid and very useful.

---

## Two Kinds of Mutability

Simple has **two orthogonal types of mutability**:

### 1. Binding Mutability (`val` vs `var`)

Can you **reassign** the variable?

```simple
val x = 10
x = 20  # ERROR - val binding is immutable

var y = 10
y = 20  # OK - var binding is mutable
```

### 2. Collection Mutability (`[]` vs `mut []`)

Can you **modify the contents** of the collection?

```simple
val arr = [1, 2, 3]
arr.pop()  # ERROR - immutable collection

val arr2 = mut [1, 2, 3]
arr2.pop()  # OK - mutable collection
```

---

## The 2×2 Matrix

These are **independent**, giving us 4 combinations:

| Syntax | Binding | Collection | Reassign? | Mutate? | Use Case |
|--------|---------|------------|-----------|---------|----------|
| `val x = [...]` | Immutable | Immutable | ❌ | ❌ | **Const data** |
| `val x = mut [...]` | Immutable | Mutable | ❌ | ✅ | **Mutable object, stable reference** ⭐ |
| `var x = [...]` | Mutable | Immutable | ✅ | ❌ | **Functional updates** |
| `var x = mut [...]` | Mutable | Mutable | ✅ | ✅ | **Full mutability** |

---

## Option 1: Independent Mutability ⭐ RECOMMENDED

**Allow all 4 combinations** - most flexible and matches real-world use cases.

### Example 1: `val` + `mut []` - Stable Reference to Mutable Object

```simple
val cache = mut {}  # Cache reference never changes, but contents do

fn add_to_cache(key: text, value: Value):
    cache[key] = value  # ✅ Mutate contents

fn clear_cache():
    cache.clear()  # ✅ Mutate contents

# cache = mut {}  # ❌ ERROR - can't reassign val binding
```

**Real-world analogy** (Java):
```java
final List<String> items = new ArrayList<>();  // final binding
items.add("hello");  // ✅ Mutate collection
items = new ArrayList<>();  // ❌ ERROR - can't reassign final
```

**Real-world analogy** (JavaScript):
```javascript
const arr = [1, 2, 3];  // const binding
arr.push(4);  // ✅ Mutate array
arr = [5, 6];  // ❌ ERROR - can't reassign const
```

**Real-world analogy** (Rust):
```rust
let cell = RefCell::new(vec![1, 2, 3]);  // let (immutable binding)
cell.borrow_mut().push(4);  // ✅ Mutate through RefCell
cell = RefCell::new(vec![5, 6]);  // ❌ ERROR - can't reassign let
```

### Example 2: `var` + `[]` - Functional Updates

```simple
var history = [initial_state]  # Binding can change, but each array is immutable

fn add_state(state: State):
    history = history + [state]  # ✅ Reassign to new array (functional)
    # history.push(state)  # ❌ ERROR - immutable collection
```

**Use case**: When you want to replace entire array but keep each version immutable (for undo/redo, snapshots, etc.)

### Example 3: `val` + `[]` - Truly Immutable

```simple
val constants = [PI, E, GOLDEN_RATIO]

# constants = [...]  # ❌ ERROR - can't reassign
# constants.push(...)  # ❌ ERROR - can't mutate
```

**Use case**: Configuration data, lookup tables, constants.

### Example 4: `var` + `mut []` - Full Mutability

```simple
var buffer = mut []  # Can both reassign and mutate

fn process():
    buffer.push(1)  # ✅ Mutate
    buffer = mut []  # ✅ Reassign to new buffer
```

**Use case**: When you need maximum flexibility.

---

## Option 2: Require `var` for `mut` Collections

**Simpler rule**: `mut` collections always require `var` binding.

```simple
var arr = mut [1, 2, 3]  # ✅ OK
val arr = mut [1, 2, 3]  # ❌ ERROR - mut requires var
```

### Rationale

- Simpler mental model: "mutable things use var"
- Avoids confusion: "why can I mutate but not reassign?"
- Easier to teach

### Counterargument

- Less flexible (can't have stable reference to mutable object)
- Doesn't match other languages (Java `final List`, JS `const arr`, Rust `let RefCell`)
- Sometimes you want: "this reference never changes, but contents can"

---

## Option 3: `mut` Implies Both Binding and Collection Mutability

**Simplest rule**: `mut` means "fully mutable" (both binding and collection).

```simple
mut arr = [1, 2, 3]  # New syntax: replaces 'var'
arr.pop()  # ✅ Mutate
arr = [4, 5]  # ✅ Reassign

val arr = [1, 2, 3]  # Immutable binding and collection
arr.pop()  # ❌ ERROR
arr = [4, 5]  # ❌ ERROR
```

### Pros
- ✅ Simplest to explain: `mut` vs `val`
- ✅ One keyword for all mutability

### Cons
- ❌ Loses distinction between binding and collection mutability
- ❌ Can't express "stable reference to mutable object"
- ❌ What about `var arr = [...]` (reassignable but immutable collection)?

---

## Comparison

| Aspect | Option 1: Independent | Option 2: Require var | Option 3: mut implies all |
|--------|----------------------|----------------------|--------------------------|
| **Flexibility** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **Simplicity** | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **Matches other languages** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **Teaching complexity** | Medium | Low | Very Low |
| **Real-world use cases** | All covered | Most covered | Some missing |

---

## Recommendation: Option 1 (Independent Mutability)

**Allow all 4 combinations**:

```simple
val x = [...]        # Immutable binding, immutable collection
val x = mut [...]    # Immutable binding, mutable collection ⭐
var x = [...]        # Mutable binding, immutable collection
var x = mut [...]    # Mutable binding, mutable collection
```

**Why**:

1. **Maximum flexibility** - covers all real-world use cases
2. **Matches established patterns**:
   - Java: `final List<T>` (stable ref, mutable contents)
   - JavaScript: `const arr = []` (stable ref, mutable contents)
   - Rust: `let cell = RefCell<T>` (stable ref, mutable contents)
3. **Clear semantics**:
   - `val`/`var` controls **binding** (reassignment)
   - `mut` controls **collection** (contents mutation)
4. **Most useful pattern**: `val arr = mut [...]` is very common
   - Class fields that never change reference
   - Global caches/registries
   - Configuration objects

---

## Implementation

### Type System

```simple
# Type annotations:
fn process(data: mut [i64]):  # Mutable collection (can be val or var)
    data.pop()  # OK

fn update(data: var mut [i64]):  # Both mutable binding and collection
    data.pop()  # OK
    data = mut [1, 2, 3]  # OK

fn read_only(data: [i64]):  # Immutable collection
    data.pop()  # ERROR
```

### Runtime Representation

```rust
pub enum Value {
    Array(Vec<Value>),                    // Immutable collection
    MutableArray(Rc<RefCell<Vec<Value>>>),  // Mutable collection
}

// In environment:
pub struct Environment {
    bindings: HashMap<String, Binding>,
}

pub struct Binding {
    value: Value,
    mutable: bool,  // Is binding itself mutable? (val vs var)
}
```

### Checks

```rust
// Reassignment check (binding mutability):
fn assign_variable(env: &mut Env, name: &str, new_value: Value) -> Result<()> {
    let binding = env.get_mut(name)?;
    if !binding.mutable {
        return Err("cannot reassign immutable binding (use 'var' instead of 'val')");
    }
    binding.value = new_value;
    Ok(())
}

// Mutation check (collection mutability):
fn call_mutating_method(receiver: &Value, method: &str) -> Result<()> {
    match receiver {
        Value::MutableArray(_) => Ok(()),  // Mutable collection - allow
        Value::Array(_) => {
            Err(format!("cannot call {} on immutable array (use 'mut [...]')", method))
        }
        _ => Err("not an array"),
    }
}
```

---

## Examples

### Example 1: Class Field (Stable Reference)

```simple
class Cache:
    items: mut {}  # Field type is mutable dict (val by default in classes)

    fn get(key: text) -> Option<Value>:
        self.items.get(key)  # ✅ Read from mutable dict

    me set(key: text, value: Value):
        self.items[key] = value  # ✅ Mutate dict contents
        # self.items = mut {}  # ❌ ERROR - can't reassign field (it's val)
```

### Example 2: Global Registry

```simple
val GLOBAL_HANDLERS = mut {}  # Never reassign, but add handlers

fn register_handler(event: text, handler: fn()):
    GLOBAL_HANDLERS[event] = handler  # ✅ Mutate contents

fn dispatch(event: text):
    val handler = GLOBAL_HANDLERS.get(event)
    handler?()

# GLOBAL_HANDLERS = mut {}  # ❌ ERROR - can't reassign val
```

### Example 3: Functional History

```simple
var history = [initial_state]  # Immutable arrays, mutable binding

fn add_state(state: State):
    history = history + [state]  # ✅ Create new array, reassign

fn undo():
    if history.len() > 1:
        history = history[0..history.len()-1]  # ✅ Slice and reassign
```

### Example 4: Mutable Buffer

```simple
var buffer = mut []  # Full mutability

fn fill_buffer():
    for i in 0..100:
        buffer.push(i)  # ✅ Mutate

fn reset_buffer():
    buffer = mut []  # ✅ Reassign to fresh buffer
```

---

## Error Messages

Make error messages clear about which mutability is violated:

```simple
val arr = [1, 2, 3]
arr.pop()
# ERROR: cannot call pop() on immutable collection
# help: use 'mut [...]' to create a mutable array
# note: the binding is immutable (val), but that's separate from collection mutability

val arr2 = mut [1, 2, 3]
arr2 = mut [4, 5, 6]
# ERROR: cannot reassign immutable binding 'arr2'
# help: use 'var arr2 = mut [...]' if you need to reassign
# note: the collection is mutable, but the binding is not

var arr3 = [1, 2, 3]
arr3.pop()
# ERROR: cannot call pop() on immutable collection
# help: use 'var arr3 = mut [...]' to create a mutable array
# note: the binding is mutable (var), but the collection is not
```

---

## Answer to Your Question

**Yes, `val arr = mut [...]` is not only possible but very useful!**

It means:
- **`val`**: Binding is immutable (can't reassign `arr`)
- **`mut []`**: Collection is mutable (can call `arr.pop()`, `arr.push()`, etc.)

This is the **most common pattern** in practice:
- Java: `final List<T> list = new ArrayList<>();`
- JavaScript: `const arr = [];`
- Rust: `let cell = RefCell::new(vec![]);`
- Python: Lists are always mutable, but you rarely reassign the variable

**Recommendation**: Allow all 4 combinations for maximum flexibility.

| Syntax | Use Case |
|--------|----------|
| `val x = [...]` | Constants, config data |
| **`val x = mut [...]`** | **Class fields, caches, registries** ⭐ |
| `var x = [...]` | Functional updates, history |
| `var x = mut [...]` | Full mutability, buffers |

The independent mutability model is most powerful and matches real-world needs.
