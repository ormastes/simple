# Verification Improvements Guide

This guide covers planned improvements to Simple's Lean 4 verification system. These features will make formal verification more practical and ergonomic.

> **Status:** Proposed features - not yet implemented

## Quick Reference

| Feature | Syntax | Purpose |
|---------|--------|---------|
| Ghost code | `@ghost fn ...` | Spec-only functions (erased at runtime) |
| Loop invariant | `invariant: cond` | Enable induction proofs for loops |
| Refinement type | `type X = Y where P` | Types with embedded predicates |
| Assert proof | `assert proof: P` | Proof obligation (must prove) |
| Assume | `assume: P` | Trusted without proof |
| Admit | `admit: P, "reason"` | Skip proof, tracked as TODO |
| Proof hint | `lean hint: "tactic"` | Guide Lean's proof search |
| Quantifiers | `forall x in R: P` | Universal/existential in specs |

## Ghost Code

Ghost functions exist only for verification - they're completely erased at compile time.

### Why Ghost Code?

Many specifications need helper functions that would be expensive to compute at runtime:

```simple
# Without ghost: this runs at runtime (O(n) overhead)
fn is_sorted(arr: [i32]) -> bool:
    for i in 0..arr.len()-1:
        if arr[i] > arr[i+1]:
            return false
    true

# With ghost: zero runtime cost
@ghost
fn sorted(arr: [i32]) -> bool:
    for i in 0..arr.len()-1:
        if arr[i] > arr[i+1]:
            return false
    true
```

### Usage

```simple
@ghost
fn sorted<T: Ord>(arr: [T]) -> bool:
    forall i in 0..arr.len()-1: arr[i] <= arr[i+1]

@ghost
fn permutation<T>(a: [T], b: [T]) -> bool:
    a.to_multiset() == b.to_multiset()

@verify
fn sort(arr: [i32]) -> [i32]:
    in: true
    out(result):
        sorted(result)              # Ghost call OK in contract
        permutation(arr, result)    # Ghost call OK in contract

    # ... implementation
    # sorted(arr)  # ERROR: can't call ghost from regular code
```

### Rules

1. Ghost functions must be pure (no side effects)
2. Ghost can call other ghost functions
3. Non-ghost code cannot call ghost functions
4. Contracts can call ghost functions

## Loop Invariants

Loop invariants specify properties that hold at each iteration, enabling induction proofs.

### Basic Syntax

```simple
@verify
fn sum(arr: [i32]) -> i64:
    out(result): result == sum_spec(arr, arr.len())

    var total: i64 = 0
    for i in 0..arr.len():
        invariant: total == sum_spec(arr, i)
        total = total + arr[i]
    total
```

### Multiple Invariants

```simple
@verify
fn find_max(arr: [i32]) -> i32:
    in: arr.len() > 0
    out(result): forall x in arr: x <= result

    var max = arr[0]
    for i in 1..arr.len():
        invariant: forall j in 0..i: arr[j] <= max
        invariant: exists j in 0..i: arr[j] == max
        if arr[i] > max:
            max = arr[i]
    max
```

### While Loops

```simple
@verify
fn gcd(a: i64, b: i64) -> i64:
    in: a > 0 && b > 0
    out(result): divides(result, a) && divides(result, b)
    decreases: b

    var x = a
    var y = b
    while y != 0:
        invariant: gcd_spec(x, y) == gcd_spec(a, b)
        val temp = y
        y = x % y
        x = temp
    x
```

## Refinement Types

Types with embedded predicates that generate proof obligations automatically.

### Defining Refinement Types

```simple
# Basic refinements
type NonZero = i64 where self != 0
type Positive = i64 where self > 0
type Percentage = f64 where 0.0 <= self && self <= 100.0

# Collection refinements
type NonEmpty<T> = [T] where self.len() > 0
type Sorted<T: Ord> = [T] where is_sorted(self)

# Bounded values
type Byte = i32 where 0 <= self && self <= 255
type Index(len: usize) = usize where self < len
```

### Using Refinement Types

```simple
# Precondition is in the type - no contract needed
fn divide(a: i64, b: NonZero) -> i64:
    a / b

fn average(nums: NonEmpty<i64>) -> i64:
    nums.sum() / nums.len()  # len() > 0 guaranteed

fn binary_search(arr: Sorted<i32>, target: i32) -> Option<usize>:
    # Sortedness is in the type
    # ...
```

### Proof Obligations

When passing a base type where a refinement is expected:

```simple
fn example(x: i64):
    # x is just i64, divide needs NonZero
    divide(10, x)  # ERROR: must prove x != 0

    if x != 0:
        divide(10, x)  # OK: condition proves refinement
```

## Verification Statements

### Assert Proof

Creates a proof obligation that must be discharged:

```simple
@verify
fn square_positive(x: i64) -> i64:
    assert proof: x * x >= 0, "squares are non-negative"
    x * x
```

### Assume

Trusts a condition without proof (use sparingly):

```simple
@verify
fn use_external(x: i64) -> i64:
    # External library guarantees this property
    assume: external_invariant(x)
    process(x)
```

> **Warning:** `assume` bypasses verification. Use only for truly external properties.

### Admit

Skips a proof but tracks it as technical debt:

```simple
@verify
fn complex_algorithm(x: i64) -> i64:
    # TODO: This needs a complex induction proof
    admit: hard_lemma(x), "blocked on library update"
    x
```

Admitted proofs appear in the verification dashboard:

```bash
simple verify --status
# Shows: ⚠ complex_algorithm: "blocked on library update"
```

## Proof Hints

Guide Lean's proof search with tactics:

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

### Referencing Lean Block Theorems

```simple
lean{
theorem sum_pos (xs : List Nat) (h : ∀ x ∈ xs, x > 0) : xs.sum > 0 := by
  induction xs <;> simp_all
}

@verify
fn sum_positive(arr: [u32]) -> u32:
    in: forall x in arr: x > 0
    out(result): result > 0

    proof uses: sum_pos

    arr.fold(0, \acc, x: acc + x)
```

## Quantifiers

First-class quantifier syntax in specifications:

```simple
# Universal quantifier
@verify
fn all_positive(arr: [i32]) -> bool:
    out(result):
        result == true => forall x in arr: x > 0
        result == false => exists x in arr: x <= 0

# Existential quantifier
@verify
fn contains(arr: [i32], target: i32) -> bool:
    out(result):
        result == true => exists i in 0..arr.len(): arr[i] == target
        result == false => forall i in 0..arr.len(): arr[i] != target
```

### Bounded vs Unbounded

```simple
# Bounded (over a range)
forall i in 0..n: P(i)
exists x in arr: Q(x)

# Unbounded (over a type)
forall x: i64: x + 0 == x
exists n: Nat: is_prime(n)
```

## Complete Example

```simple
"""
Verified insertion sort with full specification.
"""

# Ghost specifications
@ghost
fn sorted(arr: [i32]) -> bool:
    forall i in 0..arr.len()-1: arr[i] <= arr[i+1]

@ghost
fn permutation(a: [i32], b: [i32]) -> bool:
    a.to_multiset() == b.to_multiset()

# Refinement type for sorted arrays
type SortedArray = [i32] where sorted(self)

# Verified implementation
@verify
fn insertion_sort(arr: [i32]) -> SortedArray:
    out(result): permutation(arr, result)

    var result = arr.clone()

    for i in 1..result.len():
        invariant: sorted(result[0..i])
        invariant: permutation(arr, result)

        var j = i
        while j > 0 && result[j-1] > result[j]:
            invariant: permutation(arr, result)
            swap(result, j-1, j)
            j = j - 1

    lean hint: "simp [sorted, permutation, *]"
    result
```

## CLI Commands

```bash
# Verify with incremental caching
simple verify --incremental src/

# Show verification dashboard
simple verify --status

# Generate counterexamples on failure
simple verify --counterexample src/sort.spl

# Verify specific function
simple verify --function insertion_sort src/sort.spl
```

## Best Practices

### 1. Start with Ghost Specifications

Define what you want to prove before implementing:

```simple
@ghost fn spec(input) -> output: ...

@verify
fn implementation(input) -> output:
    out(result): result == spec(input)
    # ...
```

### 2. Use Refinement Types for Common Patterns

```simple
# Instead of repeating preconditions
fn f(x: i64):
    in: x != 0
fn g(x: i64):
    in: x != 0

# Use a refinement type
type NonZero = i64 where self != 0
fn f(x: NonZero): ...
fn g(x: NonZero): ...
```

### 3. Keep Invariants Simple

```simple
# Good: Simple, focused invariant
for i in 0..n:
    invariant: sum == partial_sum(arr, i)

# Avoid: Complex compound invariants
for i in 0..n:
    invariant: sum == partial_sum(arr, i) &&
               i <= n &&
               forall j in 0..i: processed[j] &&
               ...  # Too complex
```

### 4. Use Admit Strategically

```simple
# OK: Known hard proof, tracked
admit: complex_theorem, "needs library support"

# Bad: Lazy skip
admit: simple_property, "didn't feel like proving"
```

## Related Documentation

- [Lean Blocks Guide](lean_blocks.md) - Embedding custom Lean code
- [Contracts Guide](contracts.md) - Design-by-contract basics
- [Verification Plan](../design/verification_improvements_plan.md) - Technical details

## Feature Status

| Feature | Status | Target |
|---------|--------|--------|
| Ghost code | Proposed | Sprint 1 |
| Loop invariants | Proposed | Sprint 1 |
| Assert/Assume/Admit | Proposed | Sprint 2 |
| Refinement types | Proposed | Sprint 3 |
| Proof hints | Proposed | Sprint 4 |
| Incremental verification | Proposed | Sprint 5 |
| Verification dashboard | Proposed | Sprint 5 |
