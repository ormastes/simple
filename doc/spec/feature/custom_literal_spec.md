# Custom Literal Syntax

**Feature ID:** #SYNTAX-001 | **Category:** Syntax | **Status:** In Progress

_Source: `test/feature/usage/custom_literal_spec.spl`_

---

## Overview

Tests the custom collection literal syntax, specifically the `s{...}` prefix
for set literals. Verifies that set literal notation is correctly distinguished
from variable references with block syntax. Currently uses placeholder tests
as the set literal syntax is not yet fully implemented.

## Syntax

```simple
val set_val = s{1, 2, 3}
val combined = inner1.union(inner2)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 2 |

## Test Structure

### Custom Literals

- ✅ distinguishes set literals from variables
- ✅ handles nested set literals

