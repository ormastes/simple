# Line Continuation Specification

**Feature ID:** #2400 | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/line_continuation_spec.spl`_

---

## Syntax

```simple
# Explicit continuation with backslash
val sum = value1 + \
    value2 + \
    value3

# Function call with continuation
val result = add(1, \
    2, \
    3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Explicit Continuation | Backslash at line end forces continuation to next line |
| Nesting | Multiple levels of continuation allowed |
| Indentation | Improves readability but not required for continuation |

## Behavior

Line continuation:
- Backslash at end of line continues expression to next line
- Multiple continuations can be chained
- Works in expressions and function calls
- Preserves semantic meaning across line boundaries

## Note

Implicit continuation (just newlines inside parentheses/brackets/braces) is not
currently supported. Use explicit backslash continuation instead.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Line Continuation

#### explicit continuation with backslash

- ✅ continues expression with backslash
- ✅ continues function call with backslash
- ✅ combines backslash and arithmetic
- ✅ chains multiple continuations
#### continuation in various expressions

- ✅ continues binary operation
- ✅ continues comparison
- ✅ continues string concatenation
#### continuation with indentation

- ✅ works with any indentation level
- ✅ continues deeply indented code
#### practical examples

- ✅ formats long arithmetic expression
- ✅ formats function with many arguments

