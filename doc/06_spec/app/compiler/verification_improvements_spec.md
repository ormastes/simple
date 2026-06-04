# Verification Improvements Specification

> Auto-generated from `simple/std_lib/test/features/verification/verification_improvements_spec.spl`

**Feature IDs:** #VER-001 to #VER-042
**Category:** Formal Verification
**Difficulty:** 4/5
**Status:** Proposed

---

## Overview

This specification defines planned improvements to Simple's Lean 4 verification
system. Features include ghost code, loop invariants, refinement types, and
enhanced proof assistance.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Ghost Code | Functions that exist only for verification, erased at runtime |
| Loop Invariant | Conditions that hold at each loop iteration for induction proofs |
| Refinement Type | Types with embedded predicates generating proof obligations |
| Proof Hint | Tactics or strategies to guide Lean's proof search |
| Verification Statement | assert/assume/admit with different trust levels |

## Dependencies

- Lean blocks (#1100-1105)
- Contracts (CTR-*)
- @verify annotation

## Implementation Notes

- Ghost functions must be pure (no side effects)
- Loop invariants enable induction-based proofs
- Refinement types integrate with subtyping
- Incremental verification requires content hashing

---

## Test Specifications

### Ghost Code

#### Ghost Functions

Ghost code exists only for verification purposes. It is completely
erased during compilation and has zero runtime cost. Ghost functions
can express complex specifications that would be expensive to compute.

Feature ID: VER-001

##### Scenario: Basic Ghost Function

A `@ghost` function should be available in contracts and other
ghost code but not callable from regular code.

| Test | Description |
|------|-------------|
| `it "allows ghost function definition"` | @ghost annotation marks function as spec-only |
| `it "erases ghost code at runtime"` | Ghost functions have no runtime representation |

##### Scenario: Ghost in Contracts

Ghost functions can be called from contract clauses (in:, out:)
but not from regular function bodies.

| Test | Description |
|------|-------------|
| `it "allows ghost calls in preconditions"` | Ghost function call OK in `in:` clause |
| `it "allows ghost calls in postconditions"` | Ghost function call OK in `out:` clause |
| `it "rejects ghost calls in function body"` | Compile-time error for ghost calls in regular code |

##### Scenario: Ghost Purity

Ghost functions must be pure - no side effects, IO, or mutable state access.

| Test | Description |
|------|-------------|
| `it "rejects ghost functions with side effects"` | ERROR: ghost must be pure |
| `it "allows ghost to call other ghost functions"` | Ghost can call ghost |

---

### Loop Invariants

#### Loop Invariants

Loop invariants specify conditions that hold at each iteration of a loop.
They are essential for verifying loops via induction in Lean.

Feature ID: VER-002

##### Scenario: For Loop with Invariant

The `invariant:` clause appears as the first statement in a loop
body and specifies the induction hypothesis.

| Test | Description |
|------|-------------|
| `it "parses invariant clause in for loop"` | `invariant: condition` syntax recognized |
| `it "supports multiple invariants"` | Multiple invariant clauses allowed |

##### Scenario: While Loop with Invariant

While loops also support invariants for verification.

| Test | Description |
|------|-------------|
| `it "parses invariant clause in while loop"` | `invariant:` works in while loops |

##### Scenario: Invariant to Induction

Loop invariants become induction hypotheses in generated Lean.

| Test | Description |
|------|-------------|
| `it "generates induction hypothesis"` | Loop invariant becomes Lean IH |

---

### Verification Statements

#### Assert / Assume / Admit

Different trust levels for verification statements allow flexible
proof development and tracking of unproven obligations.

Feature ID: VER-003

##### Scenario: Assert Proof

`assert proof:` generates a proof obligation that must be discharged.

| Test | Description |
|------|-------------|
| `it "generates proof obligation for assert"` | Creates theorem to prove |
| `it "includes message in proof context"` | Message available in proof |

##### Scenario: Assume (Axiom)

`assume:` trusts a condition without proof. Use sparingly.

| Test | Description |
|------|-------------|
| `it "trusts condition without proof"` | Generates axiom or sorry |
| `it "emits warning for assume"` | Compiler warns about assumptions |

##### Scenario: Admit (Tracked TODO)

`admit:` skips a proof but tracks it as technical debt.

| Test | Description |
|------|-------------|
| `it "skips proof with tracking"` | Sorry with tracking metadata |
| `it "appears in verification dashboard"` | Listed in status report |

---

### Refinement Types

#### Refinement Types

Types with embedded predicates that automatically generate proof
obligations at usage sites.

Feature ID: VER-010

##### Scenario: Basic Refinement Type

`type Name = Base where predicate` creates a refined type.

| Test | Description |
|------|-------------|
| `it "parses refinement type definition"` | `type X = Y where P` syntax |
| `it "supports generic refinement types"` | `type Sorted<T> = [T] where ...` |

##### Scenario: Refinement Subtyping

Refined types are subtypes of their base types. Passing base
type where refinement expected requires proof.

| Test | Description |
|------|-------------|
| `it "allows refined type where base expected"` | NonZero <: i64 |
| `it "requires proof for base to refined"` | Must prove predicate holds |

##### Scenario: Lean Subtype Generation

Refinement types become Lean Subtype definitions.

| Test | Description |
|------|-------------|
| `it "generates Lean Subtype"` | `def X := { x : T // P x }` |

---

### Proof Hints

#### Proof Assistance

Hints and tactics to guide Lean's automated proof search.

Feature ID: VER-020

##### Scenario: Lean Hint

`lean hint: "tactic"` suggests a proof strategy.

| Test | Description |
|------|-------------|
| `it "parses lean hint statement"` | `lean hint: "..."` syntax |
| `it "applies hint in generated proof"` | Hint used in Lean output |

##### Scenario: Proof Uses

`proof uses: theorem_name` references a theorem from lean{} block.

| Test | Description |
|------|-------------|
| `it "references lean block theorem"` | Links to user-provided theorem |

---

### Quantifier Syntax

#### First-Class Quantifiers

`forall` and `exists` syntax for specifications.

Feature ID: VER-030

##### Scenario: Forall in Contracts

`forall x in range: predicate` expresses universal properties.

| Test | Description |
|------|-------------|
| `it "parses forall in postcondition"` | Universal quantifier syntax |

##### Scenario: Exists in Contracts

`exists x in range: predicate` expresses existential properties.

| Test | Description |
|------|-------------|
| `it "parses exists in postcondition"` | Existential quantifier syntax |

---

### Incremental Verification

#### Verification Caching

Cache verification results to avoid re-checking unchanged code.

Feature ID: VER-040

##### Scenario: Cached Results

Unchanged functions use cached verification results.

| Test | Description |
|------|-------------|
| `it "caches successful proofs"` | Proof results cached |
| `it "invalidates on function change"` | Cache invalidated on change |
| `it "invalidates on dependency change"` | Transitive invalidation |

---

### Verification Dashboard

#### Status Tracking

Track and display verification status across project.

Feature ID: VER-041

##### Scenario: Dashboard Output

Show proven, admitted, and pending theorems.

| Test | Description |
|------|-------------|
| `it "shows proven count"` | Count of fully proven theorems |
| `it "shows admitted with reasons"` | Admitted proofs with messages |
| `it "shows pending obligations"` | Unproven obligations listed |

---

## Examples

### Verified Sorting

A complete example showing multiple verification features together.

```simple
@ghost
fn sorted(arr: [i32]) -> bool:
    forall i in 0..arr.len()-1: arr[i] <= arr[i+1]

@ghost
fn permutation(a: [i32], b: [i32]) -> bool:
    a.to_multiset() == b.to_multiset()

type SortedArray = [i32] where sorted(self)

@verify
fn insertion_sort(arr: [i32]) -> SortedArray:
    out(result): permutation(arr, result)

    var result = arr.clone()
    for i in 1..result.len():
        invariant: sorted(result[0..i])
        invariant: permutation(arr, result)

        var j = i
        while j > 0 && result[j-1] > result[j]:
            invariant: sorted(result[0..j]) && sorted(result[j..i+1])
            swap(result, j-1, j)
            j = j - 1

    lean hint: "simp [sorted, permutation, *]"
    result
```

---

## Related Specifications

- [Lean Block Specification](lean_block_spec.md) - lean{} block syntax
- [Contracts Specification](contracts_spec.md) - Design-by-contract
- [Verification Mode](verification_mode_spec.md) - @verify annotation

---

## Implementation Roadmap

| Sprint | Features | Duration |
|--------|----------|----------|
| 1 | Ghost code, Loop invariants | 2-3 weeks |
| 2 | Assert/Assume/Admit | 1-2 weeks |
| 3 | Refinement types | 3-4 weeks |
| 4 | Proof hints | 2 weeks |
| 5 | Incremental verification, Dashboard | 2-3 weeks |

---

## Syntax Quick Reference

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

# Quantifiers
forall x in range: predicate
exists x in range: predicate
```
