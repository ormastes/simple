# Mutability Defaults Analysis - User Expectations

**Date**: 2026-01-31
**User Insight**: "var to default mutable, let set immutable when need. people think var can change instance. [] and {} are List and dict wrapper? isnt it suppose to mutable?"

---

## The Problem with Previous Design

### Previous Design (CONFUSING):

```simple
var arr = [1, 2, 3]  # Mutable binding, IMMUTABLE collection
arr.pop()  # ❌ ERROR: need 'mut [...]'
arr = [4, 5]  # ✅ OK: can reassign
```

**Pitfall**: Users see `var` and expect to mutate `arr`, but they can't!

### What Users Actually Expect:

```simple
var arr = [1, 2, 3]
arr.pop()  # Should work! I used 'var', I can change it!
```

**User mental model**: `var` = "I can change this variable" (BOTH reassign AND mutate)

---

## Analysis: What Do Collections Mean?

### Key Question: Are `[]` and `{}` Value Types or Reference Types?

**Value types** (like integers):
- Immutable by default
- Operations create new values
- `var x = 10; x = x + 1` creates new integer

**Reference types** (like arrays/dicts):
- Mutable by default
- Operations modify in-place
- `var arr = []; arr.push(1)` modifies existing array

### In Most Languages, Arrays/Dicts are Reference Types (Mutable):

**Python**:
```python
arr = [1, 2, 3]  # Mutable by default
arr.pop()  # ✅ Works
arr.append(4)  # ✅ Works
```

**JavaScript**:
```javascript
const arr = [1, 2, 3];  // const binding, mutable collection
arr.pop();  // ✅ Works - can mutate
arr = [4, 5];  // ❌ ERROR - can't reassign const
```

**Java**:
```java
final List<Integer> list = new ArrayList<>();  // final binding
list.add(1);  // ✅ Works - can mutate
list = new ArrayList<>();  // ❌ ERROR - can't reassign final
```

**C#**:
```csharp
var list = new List<int>();  // Mutable
list.Add(1);  // ✅ Works
```

**Conclusion**: `[]` and `{}` should be **mutable by default** (reference types).

---

## Proposed Design: Collections Mutable by Default ⭐

### Syntax

```simple
# Default: Collections are mutable
var arr = [1, 2, 3]  # Mutable binding + mutable collection
let arr = [1, 2, 3]  # Immutable binding + mutable collection

# Explicit immutability (rare, for functional programming):
let arr = freeze([1, 2, 3])  # Immutable binding + immutable collection
```

### Semantics

| Syntax | Binding | Collection | Reassign? | Mutate? | Example |
|--------|---------|------------|-----------|---------|---------|
| `var arr = [...]` | Mutable | Mutable | ✅ | ✅ | `arr.pop()`, `arr = [4, 5]` |
| `let arr = [...]` | Immutable | Mutable | ❌ | ✅ | `arr.pop()` only |
| `let arr = freeze([...])` | Immutable | Immutable | ❌ | ❌ | Neither |

### Benefits

1. **Matches user expectations**: `var` means "I can change this" (both ways)
2. **Matches other languages**: Python, JS, Java all have mutable collections by default
3. **Simple mental model**:
   - `var` = fully mutable
   - `let` = can't reassign, but can mutate contents (like JS `const`)
   - `freeze()` = truly immutable (rare)

---

## Keyword Choice: `val` vs `let`

### Current Simple Uses `val`:
```simple
val x = 10  # Immutable
var x = 10  # Mutable
```

### Many Languages Use `let`:
```rust
// Rust:
let x = 10;      // Immutable
let mut x = 10;  // Mutable
```

```javascript
// JavaScript:
const x = 10;  // Immutable binding
let x = 10;    // Mutable binding
```

```swift
// Swift:
let x = 10     // Immutable
var x = 10     // Mutable
```

### Recommendation: Keep `val` for Consistency

Simple already uses `val`, so keep it:
```simple
val arr = [1, 2, 3]  # Immutable binding, mutable collection (default)
var arr = [1, 2, 3]  # Mutable binding, mutable collection (default)
```

**OR** switch to `let` for broader familiarity:
```simple
let arr = [1, 2, 3]  # Immutable binding
var arr = [1, 2, 3]  # Mutable binding
```

**User preference?** The user mentioned `let` in their question, so they might prefer it.

---

## Making Collections Immutable (When Needed)

### Option 1: `freeze()` Function

```simple
# Mutable (default):
val arr = [1, 2, 3]
arr.pop()  # ✅ OK

# Immutable (explicit):
val arr = freeze([1, 2, 3])
arr.pop()  # ❌ ERROR: frozen array is immutable
```

**Implementation**:
```rust
pub fn freeze(args: &[Value]) -> Result<Value, CompileError> {
    let value = eval_arg(args, 0)?;
    match value {
        Value::MutableArray(arr) => {
            // Convert to immutable array
            let vec = arr.borrow().clone();
            Ok(Value::Array(vec))
        }
        Value::Array(arr) => {
            // Already immutable
            Ok(Value::Array(arr))
        }
        _ => Err(CompileError::semantic("freeze() requires a collection"))
    }
}
```

### Option 2: `const` Keyword

```simple
# Mutable (default):
val arr = [1, 2, 3]

# Immutable (explicit):
val arr = const [1, 2, 3]
arr.pop()  # ❌ ERROR
```

**Parser**:
```rust
fn parse_array_literal() -> Result<Expr, ParseError> {
    let is_const = consume_if_keyword("const");
    // ...
    Ok(Expr::ArrayLiteral {
        elements,
        immutable: is_const,  // Mark as immutable
    })
}
```

### Option 3: Type Annotation

```simple
# Mutable (default):
val arr = [1, 2, 3]

# Immutable (explicit):
val arr: const [i64] = [1, 2, 3]
arr.pop()  # ❌ ERROR
```

**Type system**:
```rust
pub enum Type {
    Array(Box<Type>),             // Mutable array
    ConstArray(Box<Type>),        // Immutable array
    // ...
}
```

---

## Comparison with Other Languages

### JavaScript Model (POPULAR):
```javascript
const arr = [1, 2, 3];  // Immutable binding, mutable collection
arr.push(4);  // ✅ OK
arr = [5, 6];  // ❌ ERROR
```

**In Simple**:
```simple
val arr = [1, 2, 3]  # Same semantics as JS const
arr.push(4)  # ✅ OK
arr = [5, 6]  # ❌ ERROR
```

### Python Model (SIMPLE):
```python
arr = [1, 2, 3]  # Always mutable
arr.pop()  # ✅ OK
arr = [4, 5]  # ✅ OK (reassignment is allowed)
```

**In Simple**:
```simple
var arr = [1, 2, 3]  # Same as Python
arr.pop()  # ✅ OK
arr = [4, 5]  # ✅ OK
```

### Rust Model (EXPLICIT):
```rust
let arr = vec![1, 2, 3];      // Immutable binding + immutable data
let mut arr = vec![1, 2, 3];  // Mutable binding + mutable data
```

**In Simple (proposed)**:
```simple
val arr = freeze([1, 2, 3])  # Immutable binding + immutable data
var arr = [1, 2, 3]          # Mutable binding + mutable data
```

**Recommendation**: Follow **JavaScript/Java model** (most popular):
- Collections mutable by default
- `val`/`let` controls binding (reassignment)
- Explicit `freeze()` or `const` for immutable collections (rare)

---

## Pitfalls Analysis

### Pitfall 1: `var` with Immutable Collection (MY PREVIOUS DESIGN)

```simple
var arr = [1, 2, 3]  # Mutable binding, immutable collection
arr.pop()  # ❌ ERROR: collection is immutable
```

**Problem**: User sees `var` and expects full mutability.

**Solution**: Make collections mutable by default.

### Pitfall 2: `val` with Mutable Collection (PROPOSED DESIGN)

```simple
val arr = [1, 2, 3]  # Immutable binding, mutable collection
arr.pop()  # ✅ OK: can mutate
arr = [4, 5]  # ❌ ERROR: can't reassign
```

**Is this confusing?**

**Analysis**: This matches JavaScript `const`, Java `final`, and is widely understood.

**User expectation**:
- `val` means "can't reassign the variable"
- Doesn't mean "can't change the contents"

**Analogy**:
```simple
val person = Person(name: "Alice")
person.name = "Bob"  # ✅ Can mutate fields
person = Person(name: "Charlie")  # ❌ Can't reassign variable
```

**Conclusion**: NOT a pitfall - this is expected behavior.

### Pitfall 3: Accidental Mutation

```simple
val config = {"debug": false}

fn some_function(cfg):
    cfg["debug"] = true  # Oops! Mutated global config

some_function(config)
print(config)  # {"debug": true} - unexpected mutation!
```

**Problem**: Passing mutable collections can lead to accidental mutation.

**Solution**: Use `freeze()` for truly immutable data:
```simple
val config = freeze({"debug": false})

fn some_function(cfg):
    cfg["debug"] = true  # ❌ ERROR: cannot mutate frozen dict

some_function(config)
```

**OR** Document intent with type annotations:
```simple
fn some_function(cfg: const {text: bool}):  # const param
    cfg["debug"] = true  # ❌ ERROR: parameter is const
```

### Pitfall 4: Performance of Immutable Collections

**Question**: If we support both mutable and immutable, do we need two implementations?

**Answer**: YES, but only for optimization:

```rust
pub enum Value {
    // Mutable (default) - uses RefCell for O(1) mutations:
    Array(Rc<RefCell<Vec<Value>>>),

    // Immutable (rare) - direct Vec for zero overhead:
    FrozenArray(Rc<Vec<Value>>),  // No RefCell needed
}
```

**When to use each**:
- `Array` (mutable): Default, 99% of cases
- `FrozenArray` (immutable): Constants, config data, performance-critical read-only data

---

## Final Recommendation

### Design: Collections Mutable by Default

```simple
# Mutable binding + mutable collection (default):
var arr = [1, 2, 3]
arr.pop()  # ✅ OK
arr = [4, 5]  # ✅ OK

# Immutable binding + mutable collection (like JS const):
val arr = [1, 2, 3]
arr.pop()  # ✅ OK
arr = [4, 5]  # ❌ ERROR

# Immutable binding + immutable collection (rare):
val arr = freeze([1, 2, 3])
arr.pop()  # ❌ ERROR
arr = [4, 5]  # ❌ ERROR
```

### Why This Works

1. **Matches user expectations**: `var` = can change everything
2. **Matches other languages**: Python (mutable), JS (const mutable), Java (final mutable)
3. **Simple mental model**: Collections are mutable unless explicitly frozen
4. **Performance**: Mutable by default uses RefCell, immutable (frozen) uses direct Vec
5. **Covers all use cases**:
   - `var arr = [...]` - buffers, local state (90%)
   - `val arr = [...]` - class fields, globals (9%)
   - `val arr = freeze([...])` - constants, config (1%)

### Implementation

**Runtime types**:
```rust
pub enum Value {
    Array(Rc<RefCell<Vec<Value>>>),   // Mutable (default)
    FrozenArray(Rc<Vec<Value>>),       // Immutable (explicit)
}
```

**Literal parsing**:
```rust
Expr::ArrayLiteral { elements } => {
    let values = evaluate_elements(elements)?;
    // Always create mutable by default
    Ok(Value::Array(Rc::new(RefCell::new(values))))
}
```

**freeze() function**:
```rust
"freeze" => {
    let arr = eval_arg_array(args, 0)?;
    let vec = arr.borrow().clone();
    Ok(Value::FrozenArray(Rc::new(vec)))
}
```

---

## Comparison Table

| Design | `var arr = [...]` mutate? | `val arr = [...]` mutate? | Explicit immutable? | Pitfalls |
|--------|--------------------------|--------------------------|---------------------|----------|
| **My original** | ❌ Need `mut [...]` | ❌ Need `mut [...]` | Default | `var` doesn't let you mutate 🔥 |
| **User proposal** | ✅ Yes | ✅ Yes | `freeze()` | Matches expectations ✅ |

---

## Answer to User's Questions

### Q: "var to default mutable"
**A**: YES! `var arr = [...]` creates mutable collection by default.

### Q: "let set immutable when need"
**A**: `val`/`let` controls **binding** (reassignment), not collection mutability. Use `freeze()` for immutable collections.

### Q: "people think var can change instance"
**A**: CORRECT! `var` should allow both reassignment AND mutation. Collections should be mutable by default.

### Q: "[] and {} are List and dict wrapper? isnt it suppose to mutable?"
**A**: YES! `[]` and `{}` are **reference types** and should be mutable by default, just like Python, JavaScript, Java, C#.

---

## Updated Implementation Plan

**Replace Decision #3** in the main plan:

**OLD (confusing)**:
- `var arr = [...]` → immutable collection, need `mut [...]`

**NEW (intuitive)**:
- `var arr = [...]` → mutable collection by default
- `val arr = freeze([...])` → immutable collection when needed

**Implementation changes**:
1. Make `Value::Array` use `Rc<RefCell<Vec>>` by default (2h)
2. Add `Value::FrozenArray` for immutable (1h)
3. Add `freeze()` function (1h)
4. Update method dispatch to check frozen vs mutable (1h)
5. Testing (1h)

**Total**: 6h (same as before, simpler semantics)

---

## Code Examples

### Example 1: Class Field (Typical Use)

```simple
class Cache:
    items: {}  # Mutable dict by default

    fn get(key: text) -> Option<Value>:
        self.items.get(key)  # ✅ Read

    me set(key: text, value: Value):
        self.items[key] = value  # ✅ Mutate
```

### Example 2: Global Registry

```simple
val HANDLERS = {}  # Immutable binding, mutable collection

fn register(event: text, handler: fn()):
    HANDLERS[event] = handler  # ✅ Can mutate contents

# HANDLERS = {}  # ❌ Can't reassign val
```

### Example 3: Constants

```simple
val WEEKDAYS = freeze(["Mon", "Tue", "Wed", "Thu", "Fri"])

# WEEKDAYS.push("Sat")  # ❌ ERROR: frozen array
# WEEKDAYS = [...]  # ❌ ERROR: val binding
```

### Example 4: Local Buffer

```simple
var buffer = []  # Mutable everything

buffer.push(1)  # ✅ Mutate
buffer = []  # ✅ Reassign
```

---

## Summary

**User is correct**: Collections should be **mutable by default**.

**New design**:
- `var`/`val` controls **binding** (reassignment)
- Collections are **mutable by default** (reference types)
- Use `freeze()` for **immutable collections** (rare)

**This matches**:
- User expectations (`var` = can change)
- Other languages (Python, JS, Java)
- Real-world usage (90% mutable, 10% immutable)

**Implementation**: Replace `mut` keyword with `freeze()` function, collections mutable by default.
