# Lean Block Specification

> Auto-generated from `simple/std_lib/test/features/syntax/lean_block_spec.spl`

**Feature IDs:** #1100-1105
**Category:** Syntax
**Difficulty:** 3/5
**Status:** Implemented

---

## Overview

The `lean{}` block allows embedding Lean 4 formal verification code directly
in Simple source files. This enables formal proofs to live alongside
implementation code, supporting verification-driven development.

## Syntax

### Inline Lean Code

```simple
lean{
-- Lean 4 code here
theorem my_theorem : forall n : Nat, n + 0 = n := by
    simp
}
```

### Import External Lean File

```simple
lean import "proofs/module.lean"
```

### Import with Extensions

```simple
lean import "proofs/base.lean" lean{
-- Additional Lean code extending the import
theorem extended : ... := by
    apply base_lemma
}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Inline Block | `lean{...}` embeds Lean 4 code directly (no space before brace) |
| Import | `lean import "path"` imports external Lean file |
| Contextual | `lean` is NOT a keyword to preserve module path compatibility |
| Raw Mode | Lexer collects text verbatim, tracking brace depth |

## Behavior

- `lean{...}` (no space) is tokenized as a CustomBlock
- `lean import "..."` is parsed contextually when identifier "lean" precedes "import"
- Lean blocks are collected during HIR lowering
- Generated Lean files include user-provided blocks
- Backward compatible with module paths like `verification.lean.codegen`

---

## Test Specifications

### Lean Block Inline Syntax

#### Basic Usage

The `lean{...}` syntax (no space before brace) embeds Lean 4 code
directly in Simple source files. The code is passed through verbatim
to the Lean code generator.

##### Scenario: Basic Inline Block

A `lean{...}` block should be parsed as a LeanBlock node with
inline code and no import path.

| Test | Description |
|------|-------------|
| `it "parses inline lean code"` | Validates lean block syntax is available |
| `it "preserves lean code content"` | Lean code inside braces is preserved verbatim |

##### Scenario: Nested Braces in Lean Code

Lean code often contains braces (match, structures, etc.).
The lexer tracks brace depth to correctly find the closing brace.

| Test | Description |
|------|-------------|
| `it "handles nested braces correctly"` | Lexer tracks brace depth for proper parsing |

---

### Lean Block Import Syntax

#### Import External Lean Files

The `lean import "path"` syntax imports external Lean 4 files.
Paths are relative to the source file or absolute from project root.

##### Scenario: Basic Import

`lean import "path.lean"` creates a LeanBlock with an import path
and empty inline code.

| Test | Description |
|------|-------------|
| `it "parses lean import statement"` | Import syntax is recognized |
| `it "accepts relative paths"` | Paths relative to source file location |
| `it "accepts absolute paths"` | Paths from project root starting with / |

---

### Lean Block Backward Compatibility

#### Module Path Compatibility

The word "lean" must remain valid as an identifier and module path
component to preserve backward compatibility with existing code.

##### Scenario: Module Path Component

Existing code uses paths like `verification.lean.codegen`.
This must continue to work after adding lean{} blocks.

| Test | Description |
|------|-------------|
| `it "allows lean as module path component"` | Module paths with "lean" still work |

##### Scenario: Identifier Named Lean

Variables and functions named "lean" should still work
(though discouraged for clarity).

| Test | Description |
|------|-------------|
| `it "allows lean as variable name"` | Variables can be named "lean" |

---

### Lean Block Code Generation

#### Generated Lean Output

Lean blocks are collected during HIR lowering and emitted
in generated .lean files alongside auto-generated code.

##### Scenario: User Blocks in Output

User-provided lean blocks should appear in the generated
.lean files with appropriate context comments.

| Test | Description |
|------|-------------|
| `it "includes user lean blocks in output"` | User blocks appear in generated files |
| `it "preserves block context information"` | Context like "module" or "fn:name" is preserved |

---

## Related Specifications

- [Contracts](contracts_spec.md) - Design-by-contract verification
- [Verification Mode](verification_mode_spec.md) - @verify annotation

## Implementation Notes

- **Lexer**: CustomBlock with kind="lean" for inline blocks
- **Parser**: Contextual detection of "lean" + "import" pattern
- **HIR**: HirLeanBlock type with import_path and code fields
- **Codegen**: LeanUserBlock emitted in generated .lean files

---

## Examples

### Complete Verified Module

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

end Arithmetic
}

fn add(a: i64, b: i64) -> i64:
    a + b
```

### Function with Specification

```simple
lean{
def factorial_spec (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | n + 1 => (n + 1) * factorial_spec n

theorem factorial_correct : ∀ n, factorial n = factorial_spec n := by
    intro n
    induction n <;> simp [factorial, factorial_spec, *]
}

fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)
```
