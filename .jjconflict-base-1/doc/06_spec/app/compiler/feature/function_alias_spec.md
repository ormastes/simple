# Function Alias (Deprecated Delegation)

**Feature ID:** #FWD-001 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/function_alias_spec.spl`_

---

## Overview

Tests the deprecated `fn name = target` function alias syntax that the desugar
pipeline transforms into explicit delegation. Validates basic alias calling,
return value preservation for text and integer types, alias chaining (alias of
alias), and that original functions remain callable alongside their aliases.

## Syntax

```simple
fn sum(a: i64, b: i64) -> i64:
    add(a, b)
val result = sum(3, 4)  # calls add(3, 4) via delegation
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### function alias (deprecated delegation)

#### basic alias

- ✅ calls target function
- ✅ works with zero arguments
- ✅ works with negative arguments
#### alias preserves behavior

- ✅ preserves return value for text
- ✅ preserves return value for integer
#### alias chain

- ✅ alias of alias works
- ✅ intermediate alias also works
#### original function

- ✅ original still works
- ✅ alias and original return same result
#### void alias

- ✅ void alias is callable

