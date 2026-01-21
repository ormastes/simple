# Verification Improvements Plan

**Status:** Proposed
**Category:** Formal Verification
**Priority:** High
**Dependencies:** lean{} blocks (#1100-1105), Contracts (CTR-*)

---

## Executive Summary

This document outlines planned improvements to Simple's Lean 4 verification system. The goal is to make formal verification more practical, ergonomic, and powerful while maintaining the separation between runtime contracts and formal proofs.

---

## Current State

### What Works
- `@verify` annotation triggers Lean theorem generation
- Contracts (`in:`, `out:`, `decreases:`) convert to Lean propositions
- `lean{}` blocks embed custom Lean code
- Runtime contract checking (always active)

### Limitations
- No ghost/spec-only code (runtime cost for specs)
- No loop invariants (can't verify loops)
- No inline proof hints (proofs all `sorry`)
- No refinement types (preconditions repeated everywhere)
- No incremental verification (full rebuild each time)

---

## Proposed Features

### Phase 1: Foundation (Priority: High)

#### 1.1 Ghost Code (`@ghost`)

**Feature ID:** VER-001
**Complexity:** Medium
**Impact:** High

Ghost code exists only for verification - erased at compile time.

```simple
@ghost
fn sorted<T: Ord>(arr: [T]) -> bool:
    for i in 0..arr.len()-1:
        if arr[i] > arr[i+1]:
            return false
    true

@ghost
fn permutation<T>(a: [T], b: [T]) -> bool:
    a.to_multiset() == b.to_multiset()

@verify
fn sort(arr: [i32]) -> [i32]:
    in: true
    out(result): sorted(result) && permutation(arr, result)
    # ... implementation
```

**Implementation:**
- Parser: Add `@ghost` annotation
- HIR: Mark functions as ghost, track ghost calls
- Codegen: Skip ghost functions in runtime output
- Lean: Emit ghost functions as `def` in Lean

**Verification:**
- Ghost functions can only call other ghost functions
- Non-ghost code cannot call ghost functions (except in contracts)
- Ghost functions must be pure (no side effects)

---

#### 1.2 Loop Invariants

**Feature ID:** VER-002
**Complexity:** Medium
**Impact:** High

Loop invariants are essential for verifying iterative code.

```simple
@verify
fn sum(arr: [i32]) -> i64:
    out(result): result == sum_spec(arr, arr.len())

    var total: i64 = 0
    for i in 0..arr.len():
        invariant: total == sum_spec(arr, i)
        invariant: i <= arr.len()
        total = total + arr[i]
    total
```

**Syntax Options:**

Option A: Inline invariant statement
```simple
for i in range:
    invariant: condition
    # body
```

Option B: Block-style invariant
```simple
for i in range:
    loop:
        invariant: condition1
        invariant: condition2
    # body
```

Option C: Annotation style
```simple
@invariant(total == sum_spec(arr, i))
for i in range:
    # body
```

**Recommended:** Option A (inline) - most readable, similar to Dafny/Why3.

**Implementation:**
- Parser: Allow `invariant:` as first statement in loop body
- HIR: `HirLoopInvariant` attached to loop nodes
- Lean: Generate induction hypothesis from invariant

**Generated Lean:**
```lean
theorem sum_correct (arr : List Int) :
  sum arr = sum_spec arr arr.length := by
  -- Loop converted to recursion with invariant as IH
  induction arr.length with
  | zero => simp [sum_spec]
  | succ n ih =>
    -- invariant: total == sum_spec(arr, i)
    have h_inv : total = sum_spec arr n := ih
    simp [sum_spec, h_inv]
```

---

#### 1.3 Assume / Assert / Admit

**Feature ID:** VER-003
**Complexity:** Low
**Impact:** Medium

Different trust levels for verification statements.

```simple
@verify
fn algorithm(x: i64) -> i64:
    # Assert: proof obligation generated
    assert proof: x * x >= 0, "squares are non-negative"

    # Assume: trusted without proof (axiom)
    assume: external_invariant(x)

    # Admit: proof skipped, tracked as TODO
    admit: complex_lemma(x), "TODO: prove after refactor"

    x * x
```

| Statement | Lean Output | Verification Status |
|-----------|-------------|---------------------|
| `assert proof:` | theorem with proof obligation | Must prove |
| `assume:` | `axiom` or `sorry` with warning | Trusted |
| `admit:` | `sorry` with tracking | Technical debt |

**Implementation:**
- Parser: New statement types
- HIR: `HirVerificationStatement { kind, condition, message }`
- Lean: Emit appropriate Lean construct
- Report: Track admits in verification dashboard

---

### Phase 2: Type System Integration (Priority: High)

#### 2.1 Refinement Types

**Feature ID:** VER-010
**Complexity:** High
**Impact:** High

Types with embedded predicates that generate proof obligations.

```simple
# Type aliases with refinements
type NonZero = i64 where self != 0
type Positive = i64 where self > 0
type Percentage = f64 where 0.0 <= self && self <= 100.0
type Sorted<T: Ord> = [T] where is_sorted(self)
type NonEmpty<T> = [T] where self.len() > 0

# Usage - refinements become implicit preconditions
fn divide(a: i64, b: NonZero) -> i64:
    a / b  # No precondition needed - in type

fn average(nums: NonEmpty<i64>) -> i64:
    nums.sum() / nums.len()  # len() > 0 guaranteed

fn binary_search(arr: Sorted<i32>, target: i32) -> Option<usize>:
    # Sortedness in type, not precondition
```

**Subtyping Rules:**
- `NonZero <: i64` (refinement is subtype of base)
- `Sorted<T> <: [T]`
- Passing `i64` where `NonZero` expected requires proof

**Implementation:**
- Parser: `type Name = Base where predicate`
- Type checker: Track refinements, check subtyping
- HIR: `HirRefinementType { base, predicate }`
- Lean: Generate refinement as `Subtype` or dependent type

**Generated Lean:**
```lean
def NonZero := { x : Int // x ≠ 0 }
def Sorted (α : Type) [Ord α] := { arr : List α // is_sorted arr }

def divide (a : Int) (b : NonZero) : Int :=
  a / b.val  -- b.property proves b ≠ 0
```

---

#### 2.2 Dependent Function Types

**Feature ID:** VER-011
**Complexity:** High
**Impact:** Medium

Return types that depend on input values.

```simple
# Length-preserving map
fn map<T, U>(arr: [T], f: fn(T) -> U) -> [U] where result.len() == arr.len():
    # ...

# Concatenation length
fn concat<T>(a: [T], b: [T]) -> [T] where result.len() == a.len() + b.len():
    # ...
```

---

### Phase 3: Proof Assistance (Priority: Medium)

#### 3.1 Proof Hints / Tactics

**Feature ID:** VER-020
**Complexity:** Low
**Impact:** Medium

Guide Lean's proof search with hints.

```simple
@verify
fn factorial(n: i64) -> i64:
    out(result): result > 0
    decreases: n

    if n <= 1:
        lean hint: "simp"
        1
    else:
        lean hint: "simp [factorial, Nat.mul_pos, *]"
        n * factorial(n - 1)
```

**Alternative: Proof blocks**
```simple
@verify
fn factorial(n: i64) -> i64:
    out(result): result > 0

    proof:
        by induction n with
        | zero => simp
        | succ n ih => simp [factorial, Nat.mul_pos, ih]

    if n <= 1: 1
    else: n * factorial(n - 1)
```

---

#### 3.2 Calculational Proofs

**Feature ID:** VER-021
**Complexity:** Medium
**Impact:** Medium

Step-by-step equational reasoning.

```simple
@verify
fn sum_formula(n: i64) -> i64:
    out(result): result == n * (n + 1) / 2

    calc:
        sum(0..=n)
        == sum(0..n) + n        by: "definition"
        == (n-1)*n/2 + n        by: "induction hypothesis"
        == (n-1)*n/2 + 2*n/2    by: "algebra"
        == ((n-1)*n + 2*n) / 2  by: "common denominator"
        == n * (n + 1) / 2      by: "factor"

    var total = 0
    for i in 0..=n:
        total = total + i
    total
```

---

#### 3.3 Proof Import / Reuse

**Feature ID:** VER-022
**Complexity:** Low
**Impact:** Medium

Reference existing proofs from `lean{}` blocks or external files.

```simple
lean{
theorem list_sum_pos (xs : List Nat) (h : ∀ x ∈ xs, x > 0) :
  xs.sum > 0 := by
  induction xs <;> simp_all
}

@verify
fn sum_positive(arr: [u32]) -> u32:
    in: all(arr, \x: x > 0)
    out(result): result > 0

    proof uses: list_sum_pos  # Reference lean{} theorem

    arr.fold(0, \acc, x: acc + x)
```

---

### Phase 4: Ergonomics (Priority: Medium)

#### 4.1 Quantifier Syntax

**Feature ID:** VER-030
**Complexity:** Medium
**Impact:** Medium

First-class quantifiers in specifications.

```simple
@verify
fn find(arr: [i32], target: i32) -> Option<usize>:
    out(result):
        match result:
            Some(i) => arr[i] == target
            None => forall j in 0..arr.len(): arr[j] != target

@verify
fn has_duplicate(arr: [i32]) -> bool:
    out(result):
        result == exists i, j in 0..arr.len():
            i != j && arr[i] == arr[j]
```

**Syntax:**
- `forall x in range: predicate`
- `exists x in range: predicate`
- `forall x: Type: predicate` (unbounded)

---

#### 4.2 Old Expression Enhancement

**Feature ID:** VER-031
**Complexity:** Low
**Impact:** Low

Enhanced `old()` for complex state tracking.

```simple
@verify
fn swap(arr: mut [i32], i: usize, j: usize):
    in: i < arr.len() && j < arr.len()
    out:
        arr[i] == old(arr[j])
        arr[j] == old(arr[i])
        forall k in 0..arr.len():
            k != i && k != j => arr[k] == old(arr[k])
```

---

### Phase 5: Tooling (Priority: Medium)

#### 5.1 Incremental Verification

**Feature ID:** VER-040
**Complexity:** Medium
**Impact:** High

Cache verification results, only re-verify changed code.

```bash
simple verify --incremental src/
```

```
Verification Results:
  Cached (unchanged): 45 theorems
  Re-verified: 3 theorems (2 passed, 1 failed)
  New: 2 theorems (needs proof)

  Total: 50 theorems
  Time: 2.3s (vs 45s full)
```

**Implementation:**
- Hash function signatures + contracts + body
- Store proof status in `.simple-verify-cache/`
- Invalidate on dependency changes

---

#### 5.2 Verification Dashboard

**Feature ID:** VER-041
**Complexity:** Low
**Impact:** Medium

Track verification status across project.

```bash
simple verify --status
```

```
╔══════════════════════════════════════════════════════════╗
║              Verification Dashboard                       ║
╠══════════════════════════════════════════════════════════╣
║ Status        │ Count │ Percentage                        ║
╠───────────────┼───────┼───────────────────────────────────╣
║ ✓ Proven      │   45  │ ████████████████████░░░░░░ 78%   ║
║ ⚠ Admitted    │   10  │ ████░░░░░░░░░░░░░░░░░░░░░ 17%   ║
║ ○ Pending     │    3  │ █░░░░░░░░░░░░░░░░░░░░░░░░  5%   ║
╠───────────────┴───────┴───────────────────────────────────╣
║ Technical Debt:                                           ║
║   - sort_correct (admitted): "needs termination proof"    ║
║   - tree_balanced (admitted): "complex induction"         ║
╚══════════════════════════════════════════════════════════╝
```

---

#### 5.3 Counterexample Generation

**Feature ID:** VER-042
**Complexity:** High
**Impact:** High

When verification fails, generate counterexamples.

```bash
simple verify --counterexample src/sort.spl
```

```
✗ theorem sort_preserves_length FAILED

Counterexample found:
  Input:  arr = [3, 1, 4, 1, 5]
  Output: result = [1, 1, 3, 4]  # Missing element!

  Violated: result.len() == arr.len()
  Expected: 5
  Actual:   4

  Trace:
    Line 15: dropped element at index 4
```

**Implementation:**
- Integrate with Lean's `#check_failure`
- Use QuickCheck-style random testing
- SMT solver integration (Z3/CVC5) for symbolic execution

---

## Implementation Roadmap

### Sprint 1: Ghost Code + Loop Invariants
**Duration:** 2-3 weeks
**Features:** VER-001, VER-002

Deliverables:
- [ ] `@ghost` annotation parsing and HIR
- [ ] Ghost function Lean emission
- [ ] Ghost purity checking
- [ ] `invariant:` syntax in loops
- [ ] Loop invariant Lean emission
- [ ] SSpec tests for both features

### Sprint 2: Verification Statements
**Duration:** 1-2 weeks
**Features:** VER-003

Deliverables:
- [ ] `assert proof:` statement
- [ ] `assume:` statement
- [ ] `admit:` statement with tracking
- [ ] Verification report generation

### Sprint 3: Refinement Types
**Duration:** 3-4 weeks
**Features:** VER-010

Deliverables:
- [ ] `type X = Y where predicate` syntax
- [ ] Refinement subtyping rules
- [ ] Proof obligation generation
- [ ] Lean Subtype emission

### Sprint 4: Proof Assistance
**Duration:** 2 weeks
**Features:** VER-020, VER-022

Deliverables:
- [ ] `lean hint:` syntax
- [ ] `proof uses:` references
- [ ] Proof block syntax

### Sprint 5: Tooling
**Duration:** 2-3 weeks
**Features:** VER-040, VER-041

Deliverables:
- [ ] Incremental verification cache
- [ ] Verification dashboard CLI
- [ ] Status annotations

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Lean 4 API changes | Medium | High | Pin Lean version, abstract codegen |
| Proof complexity explosion | High | Medium | Good defaults, escape hatches |
| Type system complexity | Medium | High | Incremental rollout, feature flags |
| Build time regression | Medium | Medium | Incremental verification |

---

## Success Metrics

1. **Adoption:** 20% of `@verify` functions use ghost code or invariants
2. **Proof completion:** 50% reduction in `sorry` theorems
3. **Build time:** <10% regression with incremental verification
4. **Documentation:** 100% SSpec coverage for new features

---

## Related Documents

- [Lean Block Design](lean_block_design.md) - lean{} block specification
- [Contracts Specification](../spec/contracts_spec.md) - Contract system
- [Verification Mode](../spec/verification_mode_spec.md) - @verify annotation

---

## Appendix: Full Syntax Reference

```simple
# Ghost code
@ghost
fn spec_function(...) -> T: ...

# Loop invariants
for i in range:
    invariant: condition
    body

while condition:
    invariant: loop_invariant
    body

# Verification statements
assert proof: condition, "message"
assume: condition
admit: condition, "reason"

# Refinement types
type Name = BaseType where predicate

# Proof hints
lean hint: "tactic"
proof uses: theorem_name
proof:
    lean proof here

# Quantifiers
forall x in range: predicate
exists x in range: predicate
```
