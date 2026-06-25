# Constructor Naming & Method in Class Body - Analysis & Fix

**Date:** 2026-01-23
**Status:** Root Cause Identified - Ready to Fix

---

## Question 1: Constructor Naming - `new()` vs `__init__()`

### Answer: Simple uses `fn new()` convention, NOT `__init__()`

**Simple Language Constructor Pattern:**
```simple
class MyClass:
    field: Type

    static fn new() -> MyClass:
        MyClass(field: value)

# Usage:
val instance = MyClass.new()
```

**Why `new()` not `__init__()`?**
- `new()` is a **static method** that returns a new instance
- `__init__()` is a pattern from Python/Java where it mutates an existing instance
- Simple uses Rust-style: constructor is responsible for creating AND initializing

**Examples from stdlib:**
- `HttpRequest.new(url: text) -> HttpRequest`
- `JsonParser.new(input: text) -> JsonParser`
- `StringInterner.new() -> StringInterner`
- `Graph.new(vertices: i32) -> Graph`

---

## Question 2: Why Can't Methods Be in Class Bodies? (WRONG - They Can!)

### The Real Answer: Methods CAN and SHOULD Be in Class Bodies!

**The parser is fully designed to accept methods in class bodies:**

```rust
// src/rust/parser/src/types_def/mod.rs lines 536-542
} else if self.check(&TokenKind::Fn)
    || self.check(&TokenKind::Me)        // ← Parser explicitly looks for me!
    || self.check(&TokenKind::Async)
    || self.check(&TokenKind::Static)
    || ...
{
    // Parse the method
    let item = self.parse_item()?;
    methods.push(f);  // Store in ClassDef.methods
}
```

**Both patterns work in the parser:**
```simple
# Pattern 1: Methods in class body (WORKS)
class MyClass:
    field: Type

    fn method():
        pass

    me mutable_method():
        pass

    static fn factory() -> MyClass:
        MyClass(field: value)

# Pattern 2: Methods in impl block (WORKS)
impl MyClass:
    fn another_method():
        pass
```

### So Why Do Tree-Sitter Files Fail?

**The parse error "expected Colon, found Val" is MISLEADING.**

Two different issues:

#### Issue A: When importing as modules
- Module is loaded via `use parser.treesitter.optimize.{StringInterner}`
- Interpreter tries to load and evaluate the module
- Some problem in interpreter's module evaluation causes parse error
- This is an **interpreter module loading bug**, not a parser bug

#### Issue B: Direct execution with method calls
- Parser **successfully** parses methods in class bodies ✅
- Code **runs** and creates the class instance ✅
- Code **fails** when a `me` method tries to modify `self.dict[key] = value` ❌
- Error: `semantic: invalid assignment: index assignment requires identifier as container`
- This is an **interpreter semantic error in assignment handling**

---

## The Real Bug: Interpreter Dict Assignment in Methods

### Reproduction Case (WORKING with patterns 1 & 2, FAILING with pattern 3)

**Pattern 1: Works - Static method initializing instance**
```simple
class StringInterner:
    strings: Dict<text, i32>
    next_id: i32

    static fn new() -> StringInterner:
        StringInterner(strings: {}, next_id: 0)  # ✅ Works

fn test():
    val interner = StringInterner.new()  # ✅ Works
test()
```

**Pattern 2: Works - Constructor through direct call**
```simple
fn test():
    val interner = StringInterner(strings: {}, next_id: 0)  # ✅ Works
test()
```

**Pattern 3: FAILS - Mutable method modifying dict**
```simple
class StringInterner:
    strings: Dict<text, i32>
    next_id: i32

    static fn new() -> StringInterner:
        StringInterner(strings: {}, next_id: 0)

    me intern(s: text) -> i32:
        self.strings[s] = 1  # ❌ FAILS HERE
        1

fn test():
    val interner = StringInterner.new()
    interner.intern("test")  # ❌ Fails with: "invalid assignment: index assignment requires identifier as container"
test()
```

### Root Cause

**Location:** `src/rust/compiler/src/interpreter_eval.rs` or `interpreter_call/` module

**Problem:**  When the interpreter evaluates `self.strings[s] = value` inside a mutable method:
1. It recognizes `self.strings` as accessing a field
2. It recognizes `[s]` as dictionary access
3. It tries to assign to `dict[key]`
4. The semantic checker rejects it with: "index assignment requires identifier as container"

**The issue:** The checker is too strict. It requires the container to be a **named variable** (like `mydict`), not a field access (like `self.mydict`).

**Why it fails:** The assignment handler doesn't properly handle:
- Field access expressions as assignment targets
- Chained field access (self.X[Y])
- Dictionary index assignment through field access

---

## The Fix

### Step 1: Identify the Exact Error Location

The error comes from semantic checking in assignment evaluation. Likely candidates:
1. `src/rust/compiler/src/interpreter_eval.rs` - where assignments are evaluated
2. `src/rust/compiler/src/interpreter_call/mod.rs` - where method calls happen
3. A validator that checks assignment target validity

### Step 2: Loosen Assignment Validation

Current (too strict):
```rust
if let Expr::Identifier(name) = assignment_target {
    // Only allow assigning to plain identifiers
    // Rejects self.field[key] = value
}
```

Needed:
```rust
// Allow:
// - Identifiers: `x = value`
// - Field access: `self.field = value`
// - Index access: `arr[0] = value`
// - Chained: `self.dict[key] = value`
// - Chained: `self.list[0].field = value`
match assignment_target {
    Expr::Identifier(_) => OK,
    Expr::FieldAccess { .. } => OK,
    Expr::IndexAccess { .. } => OK,
    Expr::MethodCall { .. } => Error,  // Still invalid
    _ => Error,
}
```

### Step 3: Handle Recursive Assignment

When assigning to `self.dict[key] = value`:
1. Evaluate `self` to get the instance
2. Evaluate `self.dict` to get the dictionary value
3. Evaluate `self.dict[key]` to identify the dictionary and key
4. Perform the assignment
5. Update the field in the instance

This requires proper handling of `me` methods' mutable semantics.

---

## Action Items

### High Priority: Fix Dict Assignment in Methods
**File:** `src/rust/compiler/src/interpreter_eval.rs` or related assignment handler
**Task:** Allow index assignment on field accesses (e.g., `self.dict[key] = value`)
**Testing:**
```simple
class Counter:
    counts: Dict<text, i32>

    me increment(key: text):
        self.counts[key] = self.counts.get(key).unwrap_or(0) + 1

val c = Counter(counts: {})
c.increment("a")  # Should work
```

### Medium Priority: Fix Module Import Semantic Error
**File:** `src/rust/compiler/src/interpreter_module/module_evaluator.rs`
**Task:** Investigate why modules with methods fail semantic checks
**Status:** Not yet analyzed in detail

### Documentation Update
**File:** `CLAUDE.md` (project guide)
**Update:** Add clear explanation that methods CAN and SHOULD be in class bodies

---

## Summary

### What Works Now
✅ Parser accepts methods in class bodies
✅ Parser stores them in ClassDef.methods
✅ Static methods work: `static fn new() -> MyClass`
✅ Simple field assignments work: `self.field = value`
✅ Constructors work: `MyClass(field: value)`

### What Doesn't Work Yet
❌ Mutable method dict assignments: `self.dict[key] = value`
❌ Mutable method list assignments: `self.list[i] = value`
❌ Module import evaluation for files with methods

### Fix Strategy
1. **Parser is correct** - no changes needed
2. **Grammar is correct** - methods in class bodies are intentional
3. **Interpreter has bugs**:
   - Assignment validation too strict
   - Module evaluation has issues
4. **Solution:** Fix interpreter, don't refactor 10,000+ lines of code

---

## Constructor Pattern Reference

**Correct Simple Language Constructor Pattern:**
```simple
class Point:
    x: i64
    y: i64

    static fn new(x: i64, y: i64) -> Point:
        Point(x: x, y: y)  # Constructor call

    static fn origin() -> Point:
        Point(x: 0, y: 0)  # Factory method variant

impl Point:
    me move(dx: i64, dy: i64):  # Mutable method
        self.x = self.x + dx
        self.y = self.y + dy

    fn distance() -> f64:  # Immutable method
        (self.x * self.x + self.y * self.y).sqrt()

fn test():
    val p = Point.new(3, 4)   # Use constructor
    p.move(1, 1)              # Call mutable method
    val d = p.distance()      # Call immutable method
```

**Never write `__init__` in Simple** - it's not idiomatic!
