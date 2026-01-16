# Ranges

*Source: `simple/std_lib/test/features/data_structures/ranges_spec.spl`*

---

# Ranges

**Feature ID:** #34
**Category:** Data Structures
**Difficulty:** Level 2/5
**Status:** Complete
**Implementation:** Simple

## Overview

Range expressions for iteration and slicing. Supports inclusive (start..end),
exclusive (start..<end), and unbounded ranges.

## Syntax

```simple
1..5        # Inclusive: [1,2,3,4,5]
1..<5       # Exclusive: [1,2,3,4]
0..10 by 2  # Stepped: [0,2,4,6,8,10]

for i in 1..10:
    print(i)
```

## Implementation

**Files:**
- simple/std_lib/src/core/range.spl

**Tests:**
- simple/std_lib/test/unit/core/range_spec.spl

**Dependencies:** Feature #13
**Required By:** None

## Notes

Lazy evaluation for memory efficiency. Step parameter for custom increments. Used
with for loops and slice operations.
