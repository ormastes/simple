# String Interpolation Specification

String interpolation allows embedding expressions directly in string literals using curly braces. Simple treats interpolation as the default for regular strings, with raw strings available when needed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-001 to #INTERP-020 |
| Category | Language \| Syntax |
| Status | Implemented |
| Source | `test/feature/usage/string_interpolation_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

String interpolation allows embedding expressions directly in string literals
using curly braces. Simple treats interpolation as the default for regular
strings, with raw strings available when needed.

## Syntax

```simple
val name = "Alice"
print "Hello, {name}!"          # Output: Hello, Alice!

print "Result: {2 + 3}"         # Output: Result: 5

val regex = r"pattern: \d+"     # Backslashes not escaped, no interpolation
```

## Key Concepts

| Concept | Syntax | Escaping | Interpolation |
|---------|--------|----------|---------------|
| Default String | `"..."` | Standard | Yes |
| Raw String | `r"..."` | None | No |
| Expression | `{expr}` | Within braces | Yes |
| Escape Sequence | `\n, \t, \\` | Standard | Processed |

## Behavior

- Expressions in braces are evaluated at runtime
- Any expression can appear in braces, not just variables
- Raw strings skip interpolation and escape processing

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/string_interpolation/result.json` |

## Scenarios

- interpolates variable in string
- interpolates multiple variables
- interpolates at start of string
- interpolates at end of string
- interpolates arithmetic expression
- interpolates multiplication expression
- interpolates boolean value
- interpolates false boolean value
- raw string preserves braces
- raw string preserves backslashes
- f-string basic interpolation
- f-string with expression
- f-string multiple interpolations
- f-string no interpolation
