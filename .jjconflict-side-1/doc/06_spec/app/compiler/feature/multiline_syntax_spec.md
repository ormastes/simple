# Multi-line Syntax Specification

**Feature ID:** #MULTI-001 | **Category:** Language | Syntax | **Status:** Implemented

_Source: `test/feature/usage/multiline_syntax_spec.spl`_

---

## Overview

Tests for multi-line syntax patterns including function calls spanning
multiple lines, array literals, and continuation lines.

## Syntax

```simple
# Multi-line function call
val result = function_name(
    arg1,
    arg2,
    arg3
)

# Multi-line array
val items = [
    1,
    2,
    3
]

# Line continuation with backslash
val sum = 1 + 2 + \
    3 + 4
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Multi-line Function Calls

#### basic multi-line calls

- ✅ calls function with arguments on multiple lines
- ✅ calls function with named arguments on multiple lines
#### nested function calls

- ✅ nests function calls on single line
- ✅ nests function calls on multiple lines
### Multi-line Literals

- ✅ creates multi-line array literal
- ✅ creates multi-line struct initialization
### Continuation Lines

- ✅ continues function call to next line
- ✅ continues call at same indent level
### Tuple Destructuring in Assignments

- ✅ destructures tuple from array element
- ✅ accesses tuple elements with dot notation
- ✅ destructures nested tuple data

