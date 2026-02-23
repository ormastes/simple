# Array Features Implementation Status

**Date**: 2026-02-01
**Session**: Array Mutability Implementation Attempt
**Status**: ⚠️ **BLOCKED** - Large-scale refactoring required

---

## Current State

###  Completed ✅
1. **Phase 0: Test Creation** (Complete)
   - Created 7 comprehensive SSpec test files (~119 tests)
   - Tests cover:
     - Mutable by default behavior
     - freeze() function
     - Type conversion
     - Fixed-size arrays
     - Target-based defaults
     - Custom backends

2. **Value Enum Changes** (Partial)
   - Added `FrozenArray(Arc<Vec<Value>>)` variant to Value enum
   - Added `FrozenDict(Arc<HashMap<String, Value>>)` variant
   - Changed Array from `Vec<Value>` to `Arc<RwLock<Vec<Value>>>`
   - Changed Dict from `HashMap<String, Value>` to `Arc<RwLock<HashMap<String, Value>>>`

### ❌ Blocked Issues

#### Issue #1: Arc<RwLock<>> Wrapper Breaks Existing Code

**Problem**: Wrapping Array/Dict in `Arc<RwLock<_>>` for interior mutability breaks ~335 compilation sites.

**Root cause**: The entire codebase expects to work with `Vec<Value>` and `HashMap<String, Value>` directly. Wrapping them requires:
- Calling `.read().unwrap()` or `.write().unwrap()` everywhere
- Changing pattern matches from `Value::Array(vec)` to `Value::Array(arc_rwlock)`
- Updating iteration, indexing, and method calls

**Attempted fixes**:
1. ✗ Automated sed replacements → broke pattern matching
2. ✗ Helper methods (`Value::array()`, `Value::dict()`) → still requires updating all access sites
3. ✗ Removing Arc<RwLock> wrapper → defeats purpose of interior mutability

**Error breakdown** (335 total errors):
- 141 E0308: Mismatched types
- 96 E0599: No method found (trying to call Vec methods on Arc<RwLock<Vec>>)
- 34 E0282: Type annotations needed
- 23 E0277: Trait bounds not satisfied
- 41 others

---

## Alternative Approaches

### Option A: Keep Vec/HashMap Unwrapped (Recommended)

**Design**:
- `Array(Vec<Value>)` - stays as is
- `FrozenArray(Arc<Vec<Value>>)` - new variant
- `freeze()` function performs deep copy into frozen variant
- Mutability tracked at binding level (var vs val) + method dispatch

**Pros**:
- Minimal code changes (only add frozen variants)
- No interior mutability needed
- Simpler implementation
- freeze() semantics clear (creates immutable copy)

**Cons**:
- freeze() has O(n) copy cost
- Can't have true "freeze in place" semantics

**Implementation effort**: ~4-8 hours

### Option B: Complete Arc<RwLock<>> Refactoring

**Design**: Current attempt - wrap all collections in Arc<RwLock<>>

**Pros**:
- True interior mutability
- freeze() can be O(1) (just unwrap the RwLock)

**Cons**:
- Massive refactoring (335+ error sites)
- Performance overhead (RwLock on every access)
- Complex error handling (what if lock is poisoned?)

**Implementation effort**: ~40-80 hours

### Option C: Hybrid Approach

**Design**:
- Keep `Array(Vec<Value>)` for most uses
- Add `MutableArray(Arc<RwLock<Vec<Value>>>)` for cases that need shared mutability
- Add `FrozenArray(Arc<Vec<Value>>)` for immutability
- Array literals default to `Array`, explicit `mut` makes `MutableArray`

**Pros**:
- Minimal disruption to existing code
- Supports both use cases

**Cons**:
- More complex type system
- Users need to understand three array types

**Implementation effort**: ~16-24 hours

---

## Recommended Path Forward

**Immediate action**: Choose Option A (Keep Vec/HashMap Unwrapped)

**Rationale**:
1. Pragmatic - delivers core functionality (freeze()) with minimal effort
2. User-facing semantics are clear (freeze makes a copy)
3. Can always optimize later if needed
4. Matches Python's freeze() behavior (creates immutable copy)

**Implementation steps** (Option A):
1. ✅ Value enum already has FrozenArray/FrozenDict variants
2. Revert Array/Dict back to Vec/HashMap (remove Arc<RwLock>)
3. Implement freeze() function in builtins.rs:
   ```rust
   "freeze" => {
       let val = eval_arg(args, 0)?;
       match val {
           Value::Array(vec) => Ok(Value::FrozenArray(Arc::new(vec))),
           Value::Dict(map) => Ok(Value::FrozenDict(Arc::new(map))),
           Value::FrozenArray(_) | Value::FrozenDict(_) => Ok(val), // already frozen
           _ => Err(...)
       }
   }
   ```
4. Update method dispatch to reject mutations on Frozen* variants
5. Fix non-exhaustive pattern matches (add Frozen* cases)
6. Run tests

**Estimated time**: 4-8 hours

---

## Files Modified (Current State)

**Value enum**:
- `/home/ormastes/dev/pub/simple/rust/compiler/src/value.rs` (lines 495-511)

**To be modified** (Option A):
- `rust/compiler/src/value.rs` - revert to Vec/HashMap
- `rust/compiler/src/interpreter_call/builtins.rs` - add freeze()
- `rust/compiler/src/interpreter_method/collections.rs` - handle Frozen* variants
- Pattern match sites - add Frozen* cases (~10-15 files)

---

## Decision Needed

User should decide:
- **Option A**: Simple copy-on-freeze (4-8 hours, recommended)
- **Option B**: Full Arc<RwLock> refactoring (40-80 hours)
- **Option C**: Hybrid approach (16-24 hours)

**My recommendation**: Option A, then revisit if performance becomes an issue.
