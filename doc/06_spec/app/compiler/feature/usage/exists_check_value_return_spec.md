# Existence Check Value Return (.? → T?) Specification

After the `.?` return-type change, the operator returns `T?` instead of `bool`. This enables pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100-VALUE-RETURN |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented (requires compiler rebuild) |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/feature/usage/exists_check_value_return_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

After the `.?` return-type change, the operator returns `T?` instead of `bool`.
This enables pattern binding (`if val x = expr.?:`) and nil coalescing
(`expr.? ?? default`).

## Behavior

`.?` returns `T?` — value if present, nil if absent. Option types pass through
without double-wrapping. See `doc/06_spec/app/compiler/feature/exists_check_spec.md` for the
full type/return table.

## Related

- `exists_check_spec.spl` — boolean truthiness tests
- `elif_val_pattern_binding_spec.spl` — `if val` / `elif val` patterns

## Value Return Semantics

    Verifies that `.?` returns `T?` (value if present, nil if absent),
    enabling pattern binding and nil coalescing. These tests require a
    compiler rebuild to pass — the pre-built binary returns `bool`.

### Text Nil Coalescing

        `.?` on text returns `text?`, enabling `?? default` patterns.
        Non-empty strings return the value, empty strings return nil.

### Collection Nil Coalescing

        `.?` on lists/dicts returns the collection wrapped in `T?`.
        Empty collections yield nil, enabling `?? default` fallback.

### Pattern Binding

        `.?` returns `T?`, which can be destructured with `if val`.
        The bound variable is guaranteed non-empty.

### Option Pass-Through

        `.?` on `T?` does not double-wrap. `Some(x).?` returns `Some(x)`,
        `nil.?` returns `nil`.

### Primitive Pass-Through

        Primitives are always present — `.?` wraps them in `T?`.
        Even `0` and `false` are present values.

### Method Chaining

        `.?` integrates with no-paren method calls and chaining.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/exists_check_value_return/result.json` |

## Scenarios

- returns value for non-empty string via ??
- returns default for empty string via ??
- chains multiple ?? fallbacks
- returns list for non-empty list via ??
- returns default for empty list via ??
- binds non-empty string
- skips binding for empty string
- binds non-empty list
- skips binding for empty list
- passes through Some value
- returns default for None
- binds Some value with if val
- returns number via ??
- returns zero via ??
- works with trim and ??
- returns default for empty trim result
- works with list.first and ??
- returns default for empty list.first
