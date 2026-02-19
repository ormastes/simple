# Floor Division (.fdiv) Method

**Feature ID:** OP-FDIV | **Category:** Operators | Arithmetic | **Status:** Implemented

_Source: `test/feature/usage/floor_division_fdiv_spec.spl`_

---

## Migration from // Operator

**Old syntax (deprecated):**
```simple
val result = 7 // 2  # Floor division (old)
```

**New syntax:**
```simple
val result = 7.fdiv(2)  # Floor division (new)
```

## Mathematical Definition

Floor division: ⌊a/b⌋ (always rounds towards negative infinity)

Properties:
- `a = b * a.fdiv(b) + a % b` (division algorithm)
- `a.fdiv(b)` has same sign as `a / b` when positive
- `a.fdiv(b)` rounds down for negative results

## Examples

```simple
# Positive integers
7.fdiv(2)    # → 3
10.fdiv(3)   # → 3

# Negative integers (rounds towards negative infinity)
(-7).fdiv(2)   # → -4 (not -3)
7.fdiv(-2)     # → -4 (not -3)
(-7).fdiv(-2)  # → 3

# Floating point
7.5.fdiv(2.0)    # → 3.0
(-7.5).fdiv(2.0) # → -4.0
```

## Comparison with Other Division

| Operation | 7 / 2 | -7 / 2 | 7 / -2 | -7 / -2 |
|-----------|-------|--------|--------|---------|
| Regular `/` | 3 | -3 | -3 | 3 |
| Floor `.fdiv()` | 3 | -4 | -4 | 3 |
| Truncate `.trunc()` | 3 | -3 | -3 | 3 |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 51 |

## Test Structure

### Floor Division (i64.fdiv) - Positive Integers
_Tests floor division with positive integers_

- ✅ divides evenly
- ✅ divides with remainder
- ✅ divides with large remainder
- ✅ divides exactly
- ✅ divides small by large
- ✅ divides one by one
- ✅ divides large numbers
### Floor Division (i64.fdiv) - Negative Integers
_Tests floor division with negative integers (rounds towards negative infinity)_

- ✅ divides negative by positive (rounds down)
- ✅ divides positive by negative (rounds down)
- ✅ divides negative by negative (positive result)
- ✅ divides negative evenly
- ✅ handles negative dividend with remainder
- ✅ handles negative divisor with remainder
- ✅ handles both negative with remainder
### Floor Division (i64.fdiv) - Edge Cases
_Tests edge cases for integer floor division_

- ✅ divides zero by positive
- ✅ divides zero by negative
- ✅ handles one divided by itself
- ✅ handles negative one by one
- ✅ handles one by negative one
### Floor Division (i64.fdiv) - Division Algorithm
_Verifies the division algorithm: a = b * fdiv(a,b) + a % b_

- ✅ satisfies division algorithm for positive numbers
- ✅ satisfies division algorithm for negative dividend
- ✅ satisfies division algorithm for negative divisor
- ✅ satisfies division algorithm for both negative
### Floor Division (f64.fdiv) - Positive Floats
_Tests floor division with positive floating point numbers_

- ✅ divides evenly
- ✅ divides with fractional result
- ✅ divides small by large
- ✅ divides with small quotient
- ✅ divides exactly at boundary
- ✅ divides fractional by integer
### Floor Division (f64.fdiv) - Negative Floats
_Tests floor division with negative floating point numbers_

- ✅ divides negative by positive
- ✅ divides positive by negative
- ✅ divides negative by negative
- ✅ handles negative fractional dividend
- ✅ handles negative fractional divisor
### Floor Division (f64.fdiv) - Special Float Values
_Tests floor division with special floating point values_

- ✅ handles division by very small number
- ✅ handles very large result
- ✅ handles infinity divided by finite
- ✅ handles finite divided by infinity
- ✅ handles NaN propagation
### Floor Division vs Regular Division
_Compares floor division with regular division_

- ✅ matches regular division for positive exact division
- ✅ differs from regular division when remainder exists
- ✅ differs for negative dividend
- ✅ differs for negative divisor
### Floor Division - Real World Use Cases
_Tests real-world applications of floor division_

- ✅ calculates number of pages needed
- ✅ calculates array chunk count
- ✅ calculates time in hours
- ✅ calculates grid coordinates
- ✅ rounds negative temperatures to day boundary
### Floor Division - Property Testing
_Property-based tests for floor division_

- ✅ always produces result <= regular division for negative
- ✅ always rounds down for fractional floats
- ✅ is idempotent for exact division
### Floor Division - Consistency with Math Block
_Tests that .fdiv() matches old // behavior in math blocks_

