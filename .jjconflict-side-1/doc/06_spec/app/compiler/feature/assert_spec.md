# Assert Statement Specification

**Feature ID:** #ASSERT-001 to #ASSERT-012 | **Category:** Language | Contracts | **Status:** Implemented

_Source: `test/feature/usage/assert_spec.spl`_

---

## Syntax

```simple
# Basic assert
expect(x > 0).to_equal(true)

# Assert with message
expect(x > 0, "x must be positive").to_equal(true)

# Assert in function
fn validate(x: i64) -> i64:
    expect(x >= 0, "input must be non-negative").to_equal(true)
    x * 2
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Basic Assert Statement

- ✅ basic assert compiles
- ✅ assert with message compiles
- ✅ multiple assert conditions
### Assert in Functions

- ✅ assert in function body
- ✅ multiple asserts in function
### Assert with Expressions

- ✅ assert with comparison
- ✅ assert with boolean logic
### Assert in Control Flow

- ✅ assert in if block
- ✅ assert in loop
### Assert with Function Contracts

- ✅ assert combined with contracts

