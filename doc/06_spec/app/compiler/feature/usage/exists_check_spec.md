# Existence Check Operator (.?) Specification

The `.?` operator checks if a value is "present" (non-nil AND non-empty). Returns `T?` — the value itself if present, `nil` if absent.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/feature/usage/exists_check_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

The `.?` operator checks if a value is "present" (non-nil AND non-empty).
Returns `T?` — the value itself if present, `nil` if absent.

After compiler rebuild, `.?` returns `T?` instead of `bool`, enabling
pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

## Behavior

- Option types: pass-through (Some stays Some, nil stays nil)
- Collections: returns value if non-empty, nil if empty
- Strings: returns value if non-empty, nil if ""
- Primitives: always returns value (0, false are still present)

## Related

- `presence(text) -> text?` — named equivalent for text
- `presence_trimmed(text) -> text?` — blank-aware variant

## Existence Check

    Verifies the `.?` operator that tests whether a value is
    "present" (non-nil AND non-empty). Works across Option, collections,
    strings, and primitives. Integrates with no-paren method calls.

### Option Presence

        `Some(x).?` is truthy (value exists), `None.?` is falsy.

### List Presence

        Non-empty lists are present, empty lists are absent.

### Dict Presence

        Non-empty dicts are present, empty dicts are absent.

### String Presence

        Non-empty strings are present, `""` is absent.

### Primitive Presence

        Primitives always exist — even `0` and `false` are present values.

### No-Paren + Existence

        `.?` chains with no-paren method calls for idiomatic patterns.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/exists_check/result.json` |

## Scenarios

- returns true for Some
- returns true for Some(0)
- returns false for None
- returns false for empty list
- returns true for non-empty list
- returns false for empty dict
- returns true for non-empty dict
- returns false for empty string
- returns true for non-empty string
- returns true for positive number
- returns true for zero
- returns true for false
- works with list.first.?
- returns false for empty list.first.?
- works with string.trim.?
- works with chained no-paren methods
- returns false for empty result
