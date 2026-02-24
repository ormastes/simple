# Existence Check Operator (.?) Specification

**Feature ID:** #2100 | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/exists_check_spec.spl`, `test/feature/usage/exists_check_value_return_spec.spl`_

---

The `.?` operator checks if a value is **present** (non-nil AND non-empty).
It returns `T?` — the value itself if present, `nil` if absent.

## Return Type

`.?` returns `T?` (optional), not `bool`:

| Expression | Type | Returns |
|-----------|------|---------|
| `"hello".?` | `text?` | `"hello"` (non-empty) |
| `"".?` | `text?` | `nil` (empty) |
| `[1,2].?` | `[i64]?` | `[1,2]` (non-empty) |
| `[].?` | `[i64]?` | `nil` (empty) |
| `Some(42).?` | `i64?` | `Some(42)` (pass-through) |
| `nil.?` | `T?` | `nil` (pass-through) |
| `42.?` | `i64?` | `42` (primitives always present) |

This enables pattern binding:
```simple
if val name = input.?:
    process(name)         # bound, guaranteed non-empty

val host = config.? ?? env.? ?? "localhost"
```

## Related: `presence` / `presence_trimmed`

Named text-specific alternatives in `std.text`:
- `presence(text) -> text?` — returns value if non-empty, nil if empty
- `presence_trimmed(text) -> text?` — returns value if non-blank, nil if whitespace-only

**Research:** `doc/research/text_validity_presence_pattern_2026-02-24.md`

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests (boolean semantics) | 17 |
| Tests (T? value return) | 18 |
| **Total** | **35** |

## Test Structure

### Existence Check Operator .? (boolean semantics)

#### Option type

- returns true for Some
- returns true for Some(0)
- returns false for None

#### List type

- returns false for empty list
- returns true for non-empty list

#### Dict type

- returns false for empty dict
- returns true for non-empty dict

#### String type

- returns false for empty string
- returns true for non-empty string

#### Primitive types

- returns true for positive number
- returns true for zero
- returns true for false

#### with no-paren method calls

- works with list.first.?
- returns false for empty list.first.?
- works with string.trim.?
- works with chained no-paren methods
- returns false for empty result

### Existence Check Value Return (.? -> T?)

#### nil coalescing with text

- returns value for non-empty string via ??
- returns default for empty string via ??
- chains multiple ?? fallbacks

#### nil coalescing with collections

- returns list for non-empty list via ??
- returns default for empty list via ??

#### pattern binding with if val

- binds non-empty string
- skips binding for empty string
- binds non-empty list
- skips binding for empty list

#### Option pass-through

- passes through Some value
- returns default for None
- binds Some value with if val

#### primitive values

- returns number via ??
- returns zero via ??

#### chained with methods

- works with trim and ??
- returns default for empty trim result
- works with list.first and ??
- returns default for empty list.first
