# Option Type Specification

Tests for the Option type representing values that may or may not be present, including constructors, pattern matching, and safe unwrapping mechanisms.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPT-001 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/option_type_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for the Option type representing values that may or may not be present,
including constructors, pattern matching, and safe unwrapping mechanisms.

## Syntax

```simple
val maybe_value: Option<i32> = Some(42)
val no_value: Option<text> = nil

match maybe_value:
Some(x) => print "Value is {x}"
None => print "No value"

val unwrapped = maybe_value.unwrap()           # Raises if None
val safe = maybe_value.unwrap_or(0)            # Default if None
val mapped = maybe_value.map(\x: x * 2)        # Transform if Some
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Some | Option containing a value |
| None | Option representing absence of value |
| Unwrapping | Extracting value from Option |
| Safe Unwrap | Get value or default/error handling |
| Composition | Chaining operations on Options |

## Behavior

- Option<T> is generic over type T
- Some(value) contains a value of type T
- None represents absence (no value)
- Pattern matching provides exhaustive case handling
- map/filter/flat_map for functional composition
- unwrap() raises error, unwrap_or() provides default value
- Existence check with .? operator

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/option_type/result.json` |

## Scenarios

- creates Some with value
- checks Some is some
- creates None
- uses unwrap_or for None
- maps Some value
- maps None returns None
- returns true for Some
- returns false for None
