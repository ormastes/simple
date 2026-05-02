# Elif Val/Var Pattern Binding Specification

**Feature ID:** #1001 | **Category:** Language | **Status:** Implemented

_Source: `test/feature/usage/elif_val_pattern_binding_spec.spl`_

---

## Overview

Tests for `elif val`/`elif var` pattern binding in conditional branches.
Verifies that pattern matching works correctly in elif positions,
matching the existing `if val` support.

## Syntax

```simple
if val Some(x) = expr1:
    use(x)
elif val Some(y) = expr2:
    use(y)
elif condition:
    fallback()
else:
    default()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Elif Val Pattern Binding

#### basic elif val matching

- ✅ matches elif val when if condition is false
- ✅ skips elif val when pattern does not match
- ✅ binds variable from elif val pattern
#### elif val with else fallback

- ✅ falls to else when elif val does not match
- ✅ does not reach else when elif val matches
#### multiple elif val branches

- ✅ matches first elif val pattern
- ✅ matches second elif val when first does not match
- ✅ falls through all elif val when none match
#### mixed elif and elif val

- ✅ matches regular elif before elif val
- ✅ matches elif val after failed regular elif
- ✅ matches regular elif after failed elif val
- ✅ reaches else after mixed elif failures
#### if val combined with elif val

- ✅ matches if val and skips elif val
- ✅ skips if val and matches elif val
- ✅ skips both if val and elif val to else
#### nested option patterns

- ✅ matches nested Some in elif val
- ✅ chains multiple Some patterns
#### elif val as implicit return

- ✅ returns from elif val branch
#### elif val scope isolation

- ✅ bindings do not leak to outer scope
#### elif val with nil/no-match returns nil

- ✅ returns nil when no branch matches

