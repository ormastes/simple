# Array Mutation Semantics Issue

**Date**: 2026-02-01
**Severity**: 🔴 **CRITICAL** - Tests will fail with current implementation
**Issue**: Mismatch between test expectations and implementation semantics

---

## The Problem

### What Tests Expect (Python/JS/Java style):
```simple
var arr = [1, 2, 3]
arr.push(4)           # Mutates arr in place
expect(arr).to_equal([1, 2, 3, 4])  # ✓ arr is now [1,2,3,4]
```

### What Current Implementation Does (Rust/Functional style):
```rust
// In collections.rs line 37-41:
"push" => {
    let mut new_arr = arr.to_vec();  // Creates NEW array
    new_arr.push(item);
    Value::Array(new_arr)             // Returns new array
}
```

**Result**: `arr.push(4)` returns `[1,2,3,4]` but `arr` still contains `[1,2,3]`

---

## Why This Happens

Without interior mutability, we can't mutate the Vec inside a Value::Array.

**Current structure**:
```rust
Value::Array(Vec<Value>)  // Vec is owned, can't mutate without &mut
```

When `arr.push(4)` is called:
1. Method receives `&[Value]` (immutable slice)
2. Creates new Vec with pushed item
3. Returns Value::Array(new_vec)
4. **Original binding not updated!**

---

## Solutions

### Option 1: Interior Mutability (Arc<RwLock<>>)

**Changes needed**:
```rust
Value::Array(Arc<RwLock<Vec<Value>>>)
```

**Pros**:
- ✅ True in-place mutation
- ✅ Matches Python/JS/Java semantics
- ✅ Tests pass as-is

**Cons**:
- ❌ 335 compilation errors to fix
- ❌ 40-80 hours effort
- ❌ RwLock overhead on every access
- ❌ We already rejected this approach

**Status**: Previously attempted, blocked by massive refactoring

### Option 2: Auto-Assignment Pattern

**Idea**: Make method calls automatically reassign on mutation

```rust
// Parser/interpreter transforms:
arr.push(4)  →  arr = arr.push(4)
```

**Implementation**: Modify method call handler to detect mutating methods and update binding

**Pros**:
- ✅ Minimal changes to Value enum
- ✅ Tests work as written
- ✅ Estimated 8-12 hours

**Cons**:
- ❌ Magic behavior (mutation methods auto-assign)
- ❌ Confusing for users (why does push() work but `val` fails?)
- ❌ Doesn't work with nested access: `obj.field.push(4)`

### Option 3: Mutable References in Bindings

**Idea**: Track mutable bindings and pass `&mut Vec` to methods

**Implementation**:
- `var` bindings allow mutation
- Method dispatch checks if receiver is mutable binding
- Mutate in place if allowed

**Pros**:
- ✅ Clear semantics (var = mutable, val = immutable)
- ✅ No wrapper types needed
- ✅ Matches Rust's mut model

**Cons**:
- ❌ Complex environment tracking
- ❌ Borrow checker issues
- ❌ Estimated 16-24 hours

### Option 4: Update Tests to Match Implementation

**Idea**: Accept functional-style arrays, rewrite tests

**Changes**:
```simple
# OLD (expected):
var arr = [1, 2, 3]
arr.push(4)

# NEW (functional):
var arr = [1, 2, 3]
arr = arr.push(4)
```

**Pros**:
- ✅ No code changes needed
- ✅ Simple, predictable semantics
- ✅ Immediate solution

**Cons**:
- ❌ Doesn't match user requirement ("mutable by default")
- ❌ Confusing compared to Python/JS/Java
- ❌ Breaks user's design intent

### Option 5: Hybrid - Mutable Arrays Only When Needed

**Idea**:
- Default: `Array(Vec<Value>)` - functional style
- Explicit: `MutableArray(Arc<RwLock<Vec<Value>>>)` - for mutation
- Syntax: `var mut arr = [1,2,3]` creates MutableArray

**Pros**:
- ✅ Clear opt-in for mutation
- ✅ Most code uses simple Arrays
- ✅ Matches Rust's explicit mut

**Cons**:
- ❌ Two array types confusing
- ❌ Doesn't match Python/JS/Java
- ❌ Estimated 20-30 hours

---

## Recommendation

### Short-term: Option 2 (Auto-Assignment)

**Rationale**:
- Delivers mutable-by-default semantics quickly
- Tests pass with minimal changes
- Can be refined later

**Implementation**:
1. Modify method call handler in `interpreter_method/mod.rs`
2. Detect mutating methods: push, pop, insert, remove, clear, reverse, sort
3. When called on `var` binding, update binding with returned value
4. Estimated: 8-12 hours

**Trade-offs**:
- ⚠️ "Magic" behavior, but users expect it
- ⚠️ Doesn't work for complex expressions (acceptable limitation)

### Long-term: Consider Option 1 or 3

If performance or semantics become critical, revisit:
- Option 1: Full interior mutability (40-80 hours)
- Option 3: Proper mutable references (16-24 hours)

---

## Impact on freeze()

**Current implementation**: ✅ Works correctly with functional arrays

**With Option 2**: ✅ Still works - frozen arrays reject mutations before auto-assign

**With Option 1**: ✅ Works - freeze() unwraps Arc<RwLock<>> into Arc<Vec>

**With Option 3**: ✅ Works - frozen arrays are always immutable bindings

---

## Decision Needed

**Question for user**: Which option should we pursue?

1. **Option 2** (8-12 hours) - Auto-assignment pattern (recommended)
2. **Option 1** (40-80 hours) - Full Arc<RwLock<>> refactoring
3. **Option 3** (16-24 hours) - Mutable reference tracking
4. **Option 4** (0 hours) - Update tests to functional style
5. **Option 5** (20-30 hours) - Hybrid approach

**My recommendation**: Option 2 for quick delivery, then evaluate if we need Option 1/3 later.

---

## Current Status

- ✅ freeze() implemented and working
- ✅ Frozen collections reject mutations correctly
- ❌ **BLOCKED**: Mutable collections don't mutate in place
- ❌ **Tests will fail**: ~25 tests in mutable_by_default_spec.spl

**Next steps**: Choose option and implement
