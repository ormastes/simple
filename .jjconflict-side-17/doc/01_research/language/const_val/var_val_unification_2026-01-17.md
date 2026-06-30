# Variable Declaration Keywords: Unification Proposal

**Date:** 2026-01-17
**Purpose:** Research and unify var/val/const/mut/immut keywords
**Goal:** Simplify and follow Scala style while keeping var and val

**User Requirements:**
- "var and val can not removed"
- "can unify and simplify it"
- "follow scallar if possible"
- "val also to support val x: type = 1234"

---

## Current State Analysis

### 1. Current Keywords in Simple

| Keyword | Purpose | Naming | Type Annotation | Example |
|---------|---------|--------|-----------------|---------|
| `val` | Immutable variable | lowercase | ❌ Not supported | `val x = 42` |
| `var` | Mutable variable | ends with `_` | ❌ Not supported | `var count_ = 0` |
| `const` | Compile-time constant | ALL_CAPS | ✅ Supported | `const MAX: u64 = 1024` |
| `let` | Legacy immutable | lowercase | Deprecated | Use `val` instead |
| `mut` | Legacy mutable modifier | - | Deprecated | Use `var` instead |

### 2. Scala Comparison

**Scala syntax:**
```scala
val x: Int = 42        // Immutable with type
val x = 42             // Immutable with inference
var y: Int = 0         // Mutable with type
var y = 0              // Mutable with inference
```

**Key differences:**
- ✅ Scala supports type annotations on both `val` and `var`
- ✅ Scala uses naming convention for constants (e.g., `MaxValue`)
- ❌ Scala doesn't have separate `const` keyword

---

## Problems with Current Design

### Problem 1: Inconsistent Type Annotation Support

```simple
# const - supports type annotation ✅
const MAX_SIZE: u64 = 1024

# val - does NOT support type annotation ❌
val x: u64 = 42  # SYNTAX ERROR

# Workaround: use suffix
val x = 42_u64   # Works but verbose
```

**Impact:** Confusing for users, inconsistent with Scala

### Problem 2: Redundant Keywords

- `val` and `let` both mean immutable (legacy)
- `var` and `mut` both mean mutable (legacy)
- `const` and `val` both immutable but different rules

**Confusion:** When to use which?

### Problem 3: Naming Convention Enforcement

```simple
# These work but violate conventions:
val MAX_SIZE = 1024    # Should be const
var x = 42             # Should end with _

# Parser detects pattern but doesn't enforce
```

**Impact:** Style inconsistency, no compiler errors

---

## Proposal: Scala-Style Unification

### Core Principles

1. **Keep `val` and `var`** (user requirement)
2. **Add type annotation support** to both
3. **Deprecate/remove redundant keywords** (`let`, `mut`, optionally `const`)
4. **Follow Scala semantics** where possible

### Option A: Pure Scala Style (Recommended)

**Remove `const`, unify under `val`:**

```simple
# Immutable with type inference
val x = 42
val name = "Alice"

# Immutable with type annotation
val x: u64 = 42
val name: String = "Alice"

# Mutable with type inference
var count = 0
var items = []

# Mutable with type annotation
var count: Int = 0
var items: List<String> = []

# Constants are just val with ALL_CAPS naming (convention, not enforced)
val MAX_SIZE: u64 = 1024
val PI: f64 = 3.14159
```

**Advantages:**
- ✅ Matches Scala exactly
- ✅ Simpler mental model (2 keywords instead of 5)
- ✅ Type annotations consistent across all declarations
- ✅ No confusion about const vs val

**Disadvantages:**
- ❌ Loses compile-time constant guarantee (const is special in other languages)
- ❌ Breaking change for existing code using `const`

### Option B: Keep `const` for Compile-Time Constants

**Keep `const` distinct from `val`:**

```simple
# Runtime immutable variable (can be computed)
val x: u64 = compute_value()
val name: String = read_input()

# Compile-time constant (must be literal)
const MAX_SIZE: u64 = 1024
const PI: f64 = 3.14159

# Mutable variable
var count: Int = 0
var items: List<String> = []
```

**Advantages:**
- ✅ Preserves compile-time constant semantics
- ✅ Compatible with C/Rust FFI expectations
- ✅ Clear distinction: `const` = compile-time, `val` = runtime

**Disadvantages:**
- ⚠️ Not pure Scala (Scala doesn't have `const`)
- ⚠️ Still 3 keywords instead of 2

---

## Implementation Plan

### Phase 1: Add Type Annotations to val/var (P0)

**Parser changes:** `src/parser/src/stmt_parsing/var_decl.rs`

```rust
// Current (val only):
fn parse_val(&mut self) -> Result<Stmt, ParseError> {
    self.expect(&TokenKind::Val)?;
    let name = self.expect_identifier()?;
    self.expect(&TokenKind::Eq)?;  // No type annotation support
    let value = self.parse_expr()?;
    // ...
}

// Proposed (val with optional type):
fn parse_val(&mut self) -> Result<Stmt, ParseError> {
    self.expect(&TokenKind::Val)?;
    let name = self.expect_identifier()?;

    // Optional type annotation
    let type_annotation = if self.check(&TokenKind::Colon) {
        self.advance();
        Some(self.parse_type()?)
    } else {
        None
    };

    self.expect(&TokenKind::Eq)?;
    let value = self.parse_expr()?;
    // ...
}
```

**Test cases:**

```simple
# Should all parse successfully:
val x: Int = 42
val x: u64 = 42_u64
val name: String = "Alice"
val items: List<Int> = [1, 2, 3]

var count: Int = 0
var flag: Bool = true
```

**Impact:** Fixes user request "val x: type = 1234"

### Phase 2: Deprecate Legacy Keywords (P1)

**Deprecation warnings:**

```simple
# Warn but still work:
let x = 42    # Warning: 'let' is deprecated, use 'val' instead
mut x = 42    # Warning: 'mut' is deprecated, use 'var' instead
```

**Timeline:**
- v0.2.0: Add deprecation warnings
- v0.3.0: Remove `let` and `mut` entirely

### Phase 3: Decide on const (P2 - User Input Needed)

**Option A: Keep const** (recommended)
- Preserve compile-time constant semantics
- Useful for FFI, optimizations
- Clear mental model: const=compile, val=runtime, var=mutable

**Option B: Remove const**
- Pure Scala style
- Simpler (2 keywords)
- Use `val` with ALL_CAPS for constants

**User decision needed before implementing**

---

## Comparison with Other Languages

### Scala
```scala
val x: Int = 42    // Immutable
var y: Int = 0     // Mutable
```
✅ Simple matches after Phase 1

### Rust
```rust
let x: u64 = 42;       // Immutable
let mut x: u64 = 42;   // Mutable
const MAX: u64 = 1024; // Compile-time constant
```
✅ Simple matches with Option B (keep const)

### Kotlin
```kotlin
val x: Int = 42    // Immutable
var y: Int = 0     // Mutable
const val MAX = 1024  // Compile-time constant
```
⚠️ Kotlin uses `const val` (modifier + keyword)

### Swift
```swift
let x: Int = 42    // Immutable
var y: Int = 0     // Mutable
```
✅ Swift is like Scala (no const)

---

## Breaking Changes Assessment

### Phase 1: Type Annotations (NON-BREAKING)

**All existing code still works:**
```simple
val x = 42        # Still valid (inference)
val x: Int = 42   # NEW: Also valid (annotation)
```

**Impact:** ✅ **Zero breaking changes**

### Phase 2: Deprecate let/mut (MINOR BREAKING)

**Migration:**
```simple
# Before:
let x = 42
mut y = 0

# After:
val x = 42
var y = 0
```

**Impact:** ⚠️ **Automated migration possible**

### Phase 3: Remove const (MAJOR BREAKING - if chosen)

**Migration:**
```simple
# Before:
const MAX_SIZE: u64 = 1024

# After (Option A - pure Scala):
val MAX_SIZE: u64 = 1024

# After (Option B - keep const):
const MAX_SIZE: u64 = 1024  # No change
```

**Impact:** ❌ **Breaking if Option A chosen**

---

## Recommendation

### Immediate Implementation

1. **Phase 1: Add type annotations to val/var** (P0)
   - Implement now
   - Non-breaking change
   - Fixes user's immediate request
   - Estimated: 2-3 hours

2. **Keep const keyword** (for now)
   - Preserves compile-time semantics
   - Compatible with C/Rust
   - Can revisit later

3. **Deprecate let/mut** (P1)
   - Add warnings in v0.2.0
   - Remove in v0.3.0
   - Simple migration path

### Future Considerations

- **User feedback** on const vs val for constants
- **Community preference** for Scala purity vs practical distinctions
- **FFI requirements** may necessitate keeping const

---

## Implementation Checklist

### Phase 1: Type Annotations (READY TO IMPLEMENT)

- [ ] Modify `parse_val()` to accept optional type annotation
- [ ] Modify `parse_var()` to accept optional type annotation
- [ ] Update AST to store type annotation
- [ ] Update type checker to use annotation or infer
- [ ] Add tests for val/var with type annotations
- [ ] Update documentation
- [ ] Update CLAUDE.md coding guidelines

### Phase 2: Deprecations (LATER)

- [ ] Add deprecation warnings for `let`
- [ ] Add deprecation warnings for `mut`
- [ ] Add migration guide
- [ ] Update all stdlib to use val/var
- [ ] Update all examples

### Phase 3: const Decision (USER INPUT NEEDED)

- [ ] Gather user feedback on const vs val
- [ ] Make decision: keep const or remove
- [ ] Implement chosen option
- [ ] Update documentation

---

## Conclusion

**Recommended path:**

1. ✅ **IMPLEMENT NOW:** Add type annotations to `val` and `var`
   - Fixes user request
   - Non-breaking
   - Scala-compatible
   - Estimated: 2-3 hours

2. ⏭️ **IMPLEMENT NEXT:** Deprecate `let` and `mut`
   - Simplifies language
   - Easy migration
   - Reduces confusion

3. 🤔 **DECIDE LATER:** Keep or remove `const`
   - Needs user input
   - Either option is valid
   - Can defer until feedback

**This gives us:**
- Simple, Scala-like syntax
- Type safety with annotations
- Backward compatibility (for now)
- Clear migration path

---

**Prepared by:** Claude Sonnet 4.5
**Next Step:** Implement Phase 1 (val/var type annotations)
**User Input Needed:** Decision on const keyword fate
