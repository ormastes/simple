# Floor Division (.fdiv) Method
*Source:* `test/feature/usage/floor_division_fdiv_spec.spl`
**Feature IDs:** OP-FDIV  |  **Category:** Operators | Arithmetic  |  **Status:** Implemented

## Overview



The `.fdiv()` method provides floor division functionality, replacing the old `//` operator
which is now used for parallel execution.

Floor division divides two numbers and rounds down (towards negative infinity), unlike
truncating division which rounds towards zero.

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

## Feature: Floor Division (i64.fdiv) - Positive Integers

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | divides evenly | pass |
| 2 | divides with remainder | pass |
| 3 | divides with large remainder | pass |
| 4 | divides exactly | pass |
| 5 | divides small by large | pass |
| 6 | divides one by one | pass |
| 7 | divides large numbers | pass |

**Example:** divides evenly
    Given val result = 10.fdiv(5)
    Then  expect result == 2

**Example:** divides with remainder
    Given val result = 7.fdiv(2)
    Then  expect result == 3

**Example:** divides with large remainder
    Given val result = 17.fdiv(5)
    Then  expect result == 3

**Example:** divides exactly
    Given val result = 20.fdiv(4)
    Then  expect result == 5

**Example:** divides small by large
    Given val result = 3.fdiv(7)
    Then  expect result == 0

**Example:** divides one by one
    Given val result = 1.fdiv(1)
    Then  expect result == 1

**Example:** divides large numbers
    Given val result = 1000.fdiv(7)
    Then  expect result == 142

## Feature: Floor Division (i64.fdiv) - Negative Integers

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | divides negative by positive (rounds down) | pass |
| 2 | divides positive by negative (rounds down) | pass |
| 3 | divides negative by negative (positive result) | pass |
| 4 | divides negative evenly | pass |
| 5 | handles negative dividend with remainder | pass |
| 6 | handles negative divisor with remainder | pass |
| 7 | handles both negative with remainder | pass |

**Example:** divides negative by positive (rounds down)
    Given val result = (-7).fdiv(2)
    Then  expect result == (-4)  # Not -3! Rounds towards negative infinity

**Example:** divides positive by negative (rounds down)
    Given val result = 7.fdiv(-2)
    Then  expect result == (-4)  # Not -3! Rounds towards negative infinity

**Example:** divides negative by negative (positive result)
    Given val result = (-7).fdiv(-2)
    Then  expect result == 3

**Example:** divides negative evenly
    Given val result = (-10).fdiv(-5)
    Then  expect result == 2

**Example:** handles negative dividend with remainder
    Given val result = (-17).fdiv(5)
    Then  expect result == (-4)  # -17 / 5 = -3.4 → floor = -4

**Example:** handles negative divisor with remainder
    Given val result = 17.fdiv(-5)
    Then  expect result == (-4)  # 17 / -5 = -3.4 → floor = -4

**Example:** handles both negative with remainder
    Given val result = (-17).fdiv(-5)
    Then  expect result == 3  # -17 / -5 = 3.4 → floor = 3

## Feature: Floor Division (i64.fdiv) - Edge Cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | divides zero by positive | pass |
| 2 | divides zero by negative | pass |
| 3 | handles one divided by itself | pass |
| 4 | handles negative one by one | pass |
| 5 | handles one by negative one | pass |

**Example:** divides zero by positive
    Given val result = 0.fdiv(5)
    Then  expect result == 0

**Example:** divides zero by negative
    Given val result = 0.fdiv(-5)
    Then  expect result == 0

**Example:** handles one divided by itself
    Given val result = 42.fdiv(42)
    Then  expect result == 1

**Example:** handles negative one by one
    Given val result = (-1).fdiv(1)
    Then  expect result == (-1)

**Example:** handles one by negative one
    Given val result = 1.fdiv(-1)
    Then  expect result == (-1)

## Feature: Floor Division (i64.fdiv) - Division Algorithm

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | satisfies division algorithm for positive numbers | pass |
| 2 | satisfies division algorithm for negative dividend | pass |
| 3 | satisfies division algorithm for negative divisor | pass |
| 4 | satisfies division algorithm for both negative | pass |

**Example:** satisfies division algorithm for positive numbers
    Given val a = 17
    Given val b = 5
    Given val q = a.fdiv(b)
    Given val r = a % b
    Then  expect a == b * q + r
    Then  expect q == 3
    Then  expect r == 2

**Example:** satisfies division algorithm for negative dividend
    Given val a = -17
    Given val b = 5
    Given val q = a.fdiv(b)
    Given val r = a % b
    Then  expect a == b * q + r
    Then  expect q == (-4)
    Then  expect r == 3  # Note: remainder has sign of divisor in some languages

**Example:** satisfies division algorithm for negative divisor
    Given val a = 17
    Given val b = -5
    Given val q = a.fdiv(b)
    Given val r = a % b
    Then  expect a == b * q + r
    Then  expect q == (-4)

**Example:** satisfies division algorithm for both negative
    Given val a = -17
    Given val b = -5
    Given val q = a.fdiv(b)
    Given val r = a % b
    Then  expect a == b * q + r
    Then  expect q == 3

## Feature: Floor Division (f64.fdiv) - Positive Floats

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | divides evenly | pass |
| 2 | divides with fractional result | pass |
| 3 | divides small by large | pass |
| 4 | divides with small quotient | pass |
| 5 | divides exactly at boundary | pass |
| 6 | divides fractional by integer | pass |

**Example:** divides evenly
    Given val result = 10.0.fdiv(5.0)
    Then  expect result == 2.0

**Example:** divides with fractional result
    Given val result = 7.5.fdiv(2.0)
    Then  expect result == 3.0

**Example:** divides small by large
    Given val result = 1.5.fdiv(2.0)
    Then  expect result == 0.0

**Example:** divides with small quotient
    Given val result = 2.9.fdiv(3.0)
    Then  expect result == 0.0

**Example:** divides exactly at boundary
    Given val result = 6.0.fdiv(2.0)
    Then  expect result == 3.0

**Example:** divides fractional by integer
    Given val result = 9.7.fdiv(3.0)
    Then  expect result == 3.0

## Feature: Floor Division (f64.fdiv) - Negative Floats

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | divides negative by positive | pass |
| 2 | divides positive by negative | pass |
| 3 | divides negative by negative | pass |
| 4 | handles negative fractional dividend | pass |
| 5 | handles negative fractional divisor | pass |

**Example:** divides negative by positive
    Given val result = (-7.5).fdiv(2.0)
    Then  expect result == (-4.0)  # Rounds down to -4, not up to -3

**Example:** divides positive by negative
    Given val result = 7.5.fdiv(-2.0)
    Then  expect result == (-4.0)  # Rounds down to -4

**Example:** divides negative by negative
    Given val result = (-7.5).fdiv(-2.0)
    Then  expect result == 3.0

**Example:** handles negative fractional dividend
    Given val result = (-5.9).fdiv(2.0)
    Then  expect result == (-3.0)  # -5.9 / 2.0 = -2.95 → floor = -3

**Example:** handles negative fractional divisor
    Given val result = 5.9.fdiv(-2.0)
    Then  expect result == (-3.0)  # 5.9 / -2.0 = -2.95 → floor = -3

## Feature: Floor Division (f64.fdiv) - Special Float Values

## Feature: Floor Division vs Regular Division

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches regular division for positive exact division | pass |
| 2 | differs from regular division when remainder exists | pass |
| 3 | differs for negative dividend | pass |
| 4 | differs for negative divisor | pass |

**Example:** matches regular division for positive exact division
    Given val regular = 10 / 5
    Given val floor = 10.fdiv(5)
    Then  expect regular == floor

**Example:** differs from regular division when remainder exists
    Given val regular = 7 / 2  # Truncating division: 3
    Given val floor = 7.fdiv(2)  # Floor division: 3
    Then  expect regular == floor  # Same for positive

**Example:** differs for negative dividend
    Given val regular = (-7) / 2  # Truncating: -3
    Given val floor = (-7).fdiv(2)  # Floor: -4
    Then  expect floor == (-4)
    Then  expect regular == (-3)
    Then  expect floor != regular

**Example:** differs for negative divisor
    Given val regular = 7 / (-2)  # Truncating: -3
    Given val floor = 7.fdiv(-2)  # Floor: -4
    Then  expect floor == (-4)
    Then  expect regular == (-3)
    Then  expect floor != regular

## Feature: Floor Division - Real World Use Cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calculates number of pages needed | pass |
| 2 | calculates array chunk count | pass |
| 3 | calculates time in hours | pass |
| 4 | calculates grid coordinates | pass |
| 5 | rounds negative temperatures to day boundary | pass |

**Example:** calculates number of pages needed
    Given val total_items = 25
    Given val items_per_page = 10
    Given val pages = (total_items + items_per_page - 1).fdiv(items_per_page)
    Then  expect pages == 3  # Need 3 pages for 25 items

**Example:** calculates array chunk count
    Given val array_length = 17
    Given val chunk_size = 5
    Given val chunks = array_length.fdiv(chunk_size)
    Then  expect chunks == 3  # 17 / 5 = 3 complete chunks

**Example:** calculates time in hours
    Given val minutes = 125
    Given val hours = minutes.fdiv(60)
    Then  expect hours == 2  # 125 minutes = 2 hours (plus 5 minutes)

**Example:** calculates grid coordinates
    Given val index = 23
    Given val grid_width = 8
    Given val row = index.fdiv(grid_width)
    Given val col = index % grid_width
    Then  expect row == 2  # Row 2 (0-indexed)
    Then  expect col == 7  # Column 7

**Example:** rounds negative temperatures to day boundary
    Given val hours_ago = -15
    Given val days_ago = hours_ago.fdiv(24)
    Then  expect days_ago == (-1)  # Yesterday (rounds down)

## Feature: Floor Division - Property Testing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | always produces result <= regular division for negative | pass |
| 2 | always rounds down for fractional floats | pass |
| 3 | is idempotent for exact division | pass |

**Example:** always produces result <= regular division for negative
    Given val a = -17
    Given val b = 5
    Given val floor_div = a.fdiv(b)
    Given val regular_div = a / b
    Then  expect floor_div <= regular_div

**Example:** always rounds down for fractional floats
    Given val result1 = 7.1.fdiv(2.0)
    Given val result2 = 7.9.fdiv(2.0)
    Then  expect result1 == 3.0
    Then  expect result2 == 3.0

**Example:** is idempotent for exact division
    Given val result1 = 10.fdiv(5)
    Given val result2 = result1.fdiv(1)
    Then  expect result2 == 2

## Feature: Floor Division - Consistency with Math Block


