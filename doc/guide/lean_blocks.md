# Lean Blocks: Embedding Formal Verification

This guide explains how to embed Lean 4 formal verification code directly in Simple source files using the `lean{}` block syntax.

## Quick Start

```simple
# Embed Lean 4 theorems directly in your code
lean{
theorem add_comm : ∀ a b : Nat, a + b = b + a := by
    omega
}

fn add(a: i64, b: i64) -> i64:
    a + b
```

## Syntax Overview

### Inline Lean Code

Use `lean{...}` (no space before the brace) to embed Lean 4 code:

```simple
lean{
-- Your Lean 4 code here
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos : ∀ n, factorial n > 0 := by
  intro n
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial]; omega
}
```

### Import External Lean Files

Import Lean files that live alongside your Simple code:

```simple
lean import "proofs/math_lemmas.lean"
```

Paths can be:
- **Relative**: `"proofs/module.lean"` - relative to the Simple source file
- **Absolute**: `"/verification/core.lean"` - from project root

### Import with Extensions

Import a base file and add additional proofs:

```simple
lean import "proofs/base.lean" lean{
-- Extend the imported definitions
theorem extended_lemma : ... := by
  apply base_theorem
  simp
}
```

## Use Cases

### 1. Function Specifications

Document and verify function behavior:

```simple
lean{
-- Specification for binary search
def binary_search_spec (arr : List Int) (target : Int) (result : Option Nat) : Prop :=
  match result with
  | some i => arr.get? i = some target
  | none => target ∉ arr
}

fn binary_search(arr: [i32], target: i32) -> Option<usize>:
    # Implementation...
```

### 2. Data Structure Invariants

Define and verify invariants:

```simple
lean{
-- Red-black tree invariant
def rb_invariant (t : RBTree α) : Prop :=
  balanced t ∧ ordered t ∧ color_valid t
}

struct RedBlackTree<T>:
    root: Option<Node<T>>
```

### 3. Algorithm Correctness

Prove algorithm properties:

```simple
lean{
theorem sort_preserves_elements :
  ∀ xs, (sort xs).toMultiset = xs.toMultiset := by
  sorry -- proof here

theorem sort_is_sorted :
  ∀ xs, sorted (sort xs) := by
  sorry -- proof here
}

fn sort(items: [i32]) -> [i32]:
    # Sorting implementation...
```

## Generated Output

When you run `simple gen-lean generate`, your lean blocks are included in the generated `.lean` files:

```lean
-- Auto-generated from mymodule.spl
import Mathlib.Tactic

namespace MyModule

-- User-provided Lean code (context: mymodule)
theorem add_comm : ∀ a b : Nat, a + b = b + a := by
    omega

-- Auto-generated function definitions...

end MyModule
```

## Best Practices

### 1. Keep Blocks Focused

Each lean block should have a clear purpose:

```simple
# Good: Focused block for factorial proofs
lean{
def factorial_spec (n : Nat) : Nat := ...
theorem factorial_correct : ... := ...
}

# Avoid: Giant block with unrelated proofs
```

### 2. Use Imports for Large Proofs

For substantial proof developments, use external files:

```simple
# Large proof library in separate file
lean import "proofs/sorting_theorems.lean"

# Small, local theorems inline
lean{
theorem local_helper : ... := by trivial
}
```

### 3. Document Your Proofs

Use Lean doc comments inside blocks:

```simple
lean{
/-- The factorial function is always positive -/
theorem factorial_pos : ∀ n, factorial n > 0 := by
  induction n <;> simp [factorial, *]
}
```

### 4. Organize by Module

Group related proofs with the code they verify:

```
src/
├── math/
│   ├── arithmetic.spl      # Implementation
│   └── proofs/
│       └── arithmetic.lean # External proofs
```

## File Colocation

Lean files can live alongside Simple source files in the same directory. This enables verification to be co-located with implementation.

### Directory Structure

```
src/
├── collections/
│   ├── btree.spl           # Implementation
│   ├── btree.lean          # Verification proofs (same folder)
│   ├── hashmap.spl
│   └── hashmap.lean
├── memory/
│   ├── gc.spl
│   ├── gc.lean             # Companion verification file
│   └── proofs/
│       ├── gc_safety.lean  # Extended proofs (subfolder)
│       └── gc_liveness.lean
```

### Colocation Patterns

**Pattern 1: Companion File**
```
foo.spl  →  foo.lean  (same directory)
```

**Pattern 2: Proofs Subdirectory**
```
foo.spl  →  proofs/foo_correctness.lean
```

**Pattern 3: Import from Companion**
```simple
# In foo.spl
lean import "foo.lean"  # Imports from same directory

fn bar():
    # implementation
```

### Benefits

- **Discoverability**: Proofs are easy to find next to implementation
- **Maintenance**: Changes to code and proofs happen together
- **Simple Imports**: Relative paths work naturally

## Compatibility Notes

- **Module Paths**: The word `lean` can still be used in module paths (e.g., `import verification.lean.codegen`)
- **No Space**: `lean{` requires no space; `lean {` is a syntax error
- **Brace Matching**: Nested braces in Lean code are handled correctly

## CLI Commands

```bash
# Generate Lean files from Simple sources
simple gen-lean generate

# Generate and verify with Lean 4
simple gen-lean generate --verify

# Generate specific verification project
simple gen-lean --project memory_safety
```

## Contracts and Lean Generation

### Automatic Contract Conversion

Contracts on `@verify` functions are automatically converted to Lean theorems:

```simple
@verify
fn divide(a: i64, b: i64) -> i64:
    in: b != 0
    out(result): result * b == a
    a / b
```

Generates:
```lean
theorem divide_postcondition (h1 : b ≠ 0) : result * b = a := sorry
```

### Manual vs Automatic

| Approach | Use Case |
|----------|----------|
| `lean{}` blocks | Custom theorems, helper definitions, complex proofs |
| Contract → Lean | Standard pre/post conditions on `@verify` functions |

### Combining Both

```simple
lean{
-- Helper lemma for the proof
theorem div_mul_cancel (a b : Int) (h : b ≠ 0) : (a / b) * b = a := by
  exact Int.ediv_mul_cancel (Int.dvd_refl a)
}

@verify
fn divide(a: i64, b: i64) -> i64:
    in: b != 0
    out(result): result * b == a
    a / b
```

## Future Improvements

Planned verification features (see [Verification Improvements](verification_improvements.md)):

- **Ghost code**: `@ghost fn sorted(arr) -> bool` - spec-only functions
- **Loop invariants**: `invariant: condition` in loops
- **Refinement types**: `type NonZero = i64 where self != 0`
- **Proof hints**: `lean hint: "simp [*]"` to guide proofs

## Related Documentation

- [Design Document](../design/lean_block_design.md) - Full technical specification
- [Verification Improvements](verification_improvements.md) - Planned features
- [Verification Guide](verification.md) - Using @verify annotations
- [Contracts](contracts.md) - Design-by-contract with requires/ensures

## Example: Complete Verified Module

```simple
"""
Verified arithmetic module with Lean 4 proofs.
"""

lean{
namespace Arithmetic

/-- Addition is commutative -/
theorem add_comm : ∀ a b : Int, a + b = b + a := by ring

/-- Addition is associative -/
theorem add_assoc : ∀ a b c : Int, (a + b) + c = a + (b + c) := by ring

/-- Zero is the identity for addition -/
theorem add_zero : ∀ a : Int, a + 0 = a := by ring

end Arithmetic
}

fn add(a: i64, b: i64) -> i64:
    a + b

fn sum(numbers: [i64]) -> i64:
    var total = 0
    for n in numbers:
        total = total + n
    total
```
