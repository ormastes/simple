# String Interpolation Specification

**Feature ID:** #INTERP-001 to #INTERP-020 | **Category:** Language | Syntax | **Status:** Implemented

_Source: `test/feature/usage/string_interpolation_spec.spl`_

---

## Overview

String interpolation allows embedding expressions directly in string literals
using curly braces. Simple treats interpolation as the default for regular
strings, with raw strings available when needed.

## Syntax

```simple
# Default interpolation (no special prefix needed)
val name = "Alice"
print "Hello, {name}!"          # Output: Hello, Alice!

# Expressions in braces
print "Result: {2 + 3}"         # Output: Result: 5

# Raw strings (no interpolation)
val regex = r"pattern: \d+"     # Backslashes not escaped, no interpolation
```

## Key Concepts

| Concept | Syntax | Escaping | Interpolation |
|---------|--------|----------|---------------|
| Default String | `"..."` | Standard | Yes |
| Raw String | `r"..."` | None | No |
| Expression | `{expr}` | Within braces | Yes |
| Escape Sequence | `{NL}, \t, \\` | Standard | Processed |

## Behavior

- Expressions in braces are evaluated at runtime
- Any expression can appear in braces, not just variables
- Raw strings skip interpolation and escape processing

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 14 |

## Test Structure

### Basic String Interpolation

- ✅ interpolates variable in string
- ✅ interpolates multiple variables
- ✅ interpolates at start of string
- ✅ interpolates at end of string
### Expression Interpolation

- ✅ interpolates arithmetic expression
- ✅ interpolates multiplication expression
- ✅ interpolates boolean value
- ✅ interpolates false boolean value
### Raw Strings

- ✅ raw string preserves braces
- ✅ raw string preserves backslashes
### F-String Syntax

- ✅ f-string basic interpolation
- ✅ f-string with expression
- ✅ f-string multiple interpolations
- ✅ f-string no interpolation

