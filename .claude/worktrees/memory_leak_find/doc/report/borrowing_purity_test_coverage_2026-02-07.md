# Borrowing & Purity Design Test Coverage Analysis

**Date**: 2026-02-07
**Design Doc**: `doc/design/borrowing_and_type_inference.md`
**Status**: Design approved, implementation not started

---

## Executive Summary

The design document `doc/design/borrowing_and_type_inference.md` describes a comprehensive system for:
1. Purity inference (Koka-style)
2. `pure fn` explicit annotation
3. `mu` as alias for `me`
4. `with x:` / `with mu x:` borrowing scopes
5. Purity-borrow rule (borrowed values only passable to pure functions)

**Current test coverage**: **Partial infrastructure, no new features tested**

---

## What Tests Exist

### 1. Borrow Checking Infrastructure (`test/compiler/borrow_check_spec.spl`)

**Status**: ✅ Complete for old Rust-style system
**Lines**: 453 lines
**Coverage**:
- Lifetimes (Named, Anonymous, Static)
- Regions and lifetime constraints
- Lifetime inference algorithm
- Places (locals, derefs, field access)
- Borrow kinds (Shared, Mutable, Unique)
- Borrow graph and NLL checker
- Control flow graph
- Liveness analysis

**Gap**: This tests the **old Rust-style lifetime system**, NOT the new purity-based system from the design doc.

### 2. Effect Inference (`test/compiler/effect_inference_spec.spl`)

**Status**: ⚠️ Skipped (modules not available in runtime)
**Lines**: 179 lines
**Coverage**:
- Pure expressions (literals, arithmetic)
- Method calls → IO effects
- Assignment → Mutates effect
- Effect merging
- Effect compatibility checking
- Custom effects by name

**Gap**: Tests basic effect tracking but NOT:
- Koka-style fixed-point inference
- `pure fn` syntax
- Purity-borrow rule
- Effect polymorphism for lambdas

### 3. Effect System (`test/system/features/effects/effect_system_spec.spl`)

**Status**: ⚠️ Pending + Skipped (async keyword unsupported)
**Lines**: 100+ lines (partial read)
**Coverage**:
- `@pure`, `@io`, `@net`, `@fs`, `@unsafe`, `@async` annotations
- Effect propagation
- Capability requirements

**Gap**: Uses **annotation-based system** (`@pure`), NOT the inference-based system from design doc.

### 4. Borrowing Feature Spec (`test/system/features/borrowing/borrowing_spec.spl`)

**Status**: ⚠️ Pending (empty stubs)
**Lines**: 36 lines
**Coverage**:
- Stubs for immutable/mutable/isolated references
- Ownership transfer stubs

**Gap**: All tests are `skip` placeholders. No actual implementation.

---

## What's Missing (According to Design Doc)

### Phase 1: Purity Inference Engine (12-16h)

**No tests for:**
- ❌ Fixed-point iteration algorithm for effect inference
- ❌ Effect propagation through call graph
- ❌ Detection of impure operations:
  - `print` → `<console>`
  - `file_*` → `<io>`
  - Global variable writes → `<mutation>`
- ❌ Effect categories: `total`, `<console>`, `<io>`, `<mutation>`, `<async>`

**Expected test file**: `test/compiler/purity_inference_spec.spl` (does not exist)

### Phase 2: `pure fn` Syntax (8-12h)

**No tests for:**
- ❌ `pure fn` keyword parsing
- ❌ Compiler verification that `pure fn` body is truly pure
- ❌ Error messages when `pure fn` calls impure functions
- ❌ Error messages when `pure fn` modifies globals

**Expected examples**:
```simple
pure fn add(a, b): a + b               # OK
# pure fn bad(): print "x"             # ERROR: pure fn cannot call print
```

**Expected test file**: `test/compiler/pure_fn_syntax_spec.spl` (does not exist)

### Phase 3: `mu` Alias (2-4h)

**No tests for:**
- ❌ `mu` as synonym for `me` in method definitions
- ❌ Both `me increment():` and `mu increment():` accepted
- ❌ AST treats both identically

**Expected test file**: `test/syntax/mu_alias_spec.spl` (does not exist)

### Phase 4: `with` Borrow Scoping (12-16h)

**No tests for:**
- ❌ `with x:` immutable borrow syntax
- ❌ `with mu x:` mutable borrow syntax
- ❌ `with x as alias:` aliasing syntax
- ❌ Original variable blocked during borrow scope
- ❌ Borrow released after scope ends
- ❌ Disambiguation from resource `with File.open() as f:`

**Expected examples**:
```simple
var data = mut [1, 2, 3]
with data:
    val n = count(data)     # OK: count is pure
    # data.push(4)          # ERROR: immutable borrow
# data is released
data.push(4)                # OK: outside borrow
```

**Expected test file**: `test/compiler/with_borrow_spec.spl` (does not exist)

### Phase 5: Purity-Borrow Rule (8-12h)

**No tests for:**
- ❌ Borrowed value passable to pure functions
- ❌ Borrowed value NOT passable to impure functions
- ❌ Error: "cannot pass borrowed value to impure function"
- ❌ Mutation allowed in `with mu` scope
- ❌ Pure reading allowed in `with mu` scope

**Expected examples**:
```simple
with data:
    val n = count(data)     # OK: count is pure
    # save(data)            # ERROR: save is impure
```

**Expected test file**: `test/compiler/purity_borrow_rule_spec.spl` (does not exist)

### Phase 6: Lambda Purity Inference (8-12h)

**No tests for:**
- ❌ Pure lambda: `\x: x * 2` inferred as `total`
- ❌ Impure lambda: `\x: print x` inferred as `<console>`
- ❌ Lambda type syntax: `fn(T) -> U` vs `mu(T) -> U`
- ❌ Pure lambda passable where `fn` parameter expected
- ❌ Impure lambda NOT passable where `fn` parameter expected
- ❌ Subtyping: `fn <: mu`

**Expected examples**:
```simple
fn apply_pure(f: fn(i64) -> i64, x: i64): f(x)
val double = \x: x * 2                          # Inferred: fn (pure)
val logger = \x: print x; x * 2                 # Inferred: mu (impure)
apply_pure(double, 5)                            # OK
# apply_pure(logger, 5)                          # ERROR: mu not assignable to fn
```

**Expected test file**: `test/compiler/lambda_purity_spec.spl` (does not exist)

### Comprehensive Examples (Section 12)

**No tests for:**
- ❌ Example 12.1: Basic purity inference
- ❌ Example 12.2: Borrowing with `with`
- ❌ Example 12.3: Effect polymorphism (`map`/`filter`/`fold`)
- ❌ Example 12.4: Classes with `mu`
- ❌ Example 12.5: Lambda types in function signatures

**Expected test file**: `test/system/features/borrowing_purity_examples_spec.spl` (does not exist)

---

## Lean Verification (Section 11)

**No verification files for:**
- ❌ `verification/purity/effect_propagation.lean` (Obligation 1)
- ❌ `verification/purity/fixed_point.lean` (Obligation 2)
- ❌ `verification/purity/total_soundness.lean` (Obligation 3)
- ❌ `verification/borrow/no_escape.lean` (Obligation 4)
- ❌ `verification/borrow/exclusivity.lean` (Obligation 5)
- ❌ `verification/borrow/release.lean` (Obligation 6)
- ❌ `verification/borrow/passing_sound.lean` (Obligation 7)

**Directory**: `verification/` exists but no purity/borrow proofs

---

## Test Coverage Summary

| Phase | Feature | Test File | Status |
|-------|---------|-----------|--------|
| 1 | Purity inference engine | `test/compiler/purity_inference_spec.spl` | ❌ Missing |
| 2 | `pure fn` syntax | `test/compiler/pure_fn_syntax_spec.spl` | ❌ Missing |
| 3 | `mu` alias | `test/syntax/mu_alias_spec.spl` | ❌ Missing |
| 4 | `with` borrow scoping | `test/compiler/with_borrow_spec.spl` | ❌ Missing |
| 5 | Purity-borrow rule | `test/compiler/purity_borrow_rule_spec.spl` | ❌ Missing |
| 6 | Lambda purity | `test/compiler/lambda_purity_spec.spl` | ❌ Missing |
| Examples | Comprehensive | `test/system/features/borrowing_purity_examples_spec.spl` | ❌ Missing |
| Verification | Lean proofs | `verification/purity/*.lean`, `verification/borrow/*.lean` | ❌ Missing |

**Total**: 0/8 test suites exist (0% coverage)

---

## Infrastructure Status

| Component | Status | Notes |
|-----------|--------|-------|
| Old borrow checker | ✅ Complete | 453-line test suite, Rust-style lifetimes |
| Old effect system | ⚠️ Partial | Exists but skipped, annotation-based |
| New purity inference | ❌ Not started | No implementation, no tests |
| New `with` syntax | ❌ Not started | Parser doesn't support it |
| `pure fn` keyword | ❌ Not started | Not in lexer/parser |
| `mu` keyword | ❌ Not started | Not in lexer/parser |

---

## Recommendations

### Priority 1: Phase 1-2 (Foundation)
1. Implement purity inference engine (Phase 1)
2. Add `pure fn` syntax (Phase 2)
3. Write comprehensive tests for both

**Estimated effort**: 20-28h implementation + 8-12h testing

### Priority 2: Phase 3-4 (Syntax)
4. Add `mu` alias (Phase 3)
5. Implement `with`/`with mu` scoping (Phase 4)
6. Write syntax and scoping tests

**Estimated effort**: 14-20h implementation + 6-8h testing

### Priority 3: Phase 5-6 (Integration)
7. Enforce purity-borrow rule (Phase 5)
8. Add lambda purity inference (Phase 6)
9. Write integration tests

**Estimated effort**: 16-24h implementation + 8-12h testing

### Priority 4: Verification
10. Write Lean4 proofs for 7 obligations
11. Integrate verification into CI

**Estimated effort**: 40-60h (proof engineering)

---

## Conclusion

**The design doc is complete and approved, but implementation has not started.**

- **Design**: 720 lines, comprehensive, single unified design ✅
- **Implementation**: 0% complete (no new keywords, no new compiler passes) ❌
- **Tests**: 0% coverage (all 8 test suites missing) ❌
- **Verification**: 0% complete (no Lean proofs) ❌

**Next step**: Begin Phase 1 (Purity inference engine) with TDD approach.

**Blocker**: Need to decide if this is v0.5.0 or v1.0.0 feature (breaking change to effect system).
