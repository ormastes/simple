# Loop Constructs Specification

**Feature ID:** #1100 | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/loops_spec.spl`_

---

## Syntax

```simple
# While loop (condition-based)
var i = 0
while i < 10:
    print i
    i = i + 1

# For loop (collection iteration)
for item in items:
    print item

# Range iteration
for i in 0..10:
    print i

# List comprehension
[for x in items if x > 5: x * 2]

# Dictionary comprehension
{for x in items: (x, x * 2)}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| While Loop | Condition-based repetition until condition becomes false |
| For Loop | Iteration over collection elements with implicit binding |
| Range | Sequence of values from start to end (inclusive or exclusive) |
| Comprehension | Concise syntax for building collections from iterations |
| Break Statement | Exit loop immediately |
| Continue Statement | Skip to next loop iteration |

## Behavior

Loop constructs:
- Execute code zero or more times based on conditions or collection size
- Support break and continue for flow control
- Provide implicit iteration variables in for loops
- Enable collection creation through comprehensions
- Work with ranges and user-defined iterables
- Support nested loops and complex conditions

## Related Specifications

- Range Expressions (start..end syntax)
- Collection Types (List, Dict, Set iteration)
- Pattern Matching (destructuring in for loops)
- Lambda Expressions (used in functional iteration)

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### Loop Constructs

#### while loops

- ✅ executes while loop with condition
- ✅ exits while loop when condition becomes false
- ✅ handles while loop with break
- ✅ handles while loop with continue
#### for loops over ranges

- ✅ iterates over exclusive range
- ✅ iterates over inclusive range
- ✅ handles negative ranges
#### for loops over collections

- ✅ iterates over list
- ✅ iterates with break
- ✅ iterates with continue
#### nested loops

- ✅ executes nested loops
- ✅ breaks outer loop from nested loop
#### list comprehensions

- ✅ creates list from range
- ✅ filters with comprehension
- ✅ transforms and filters
- ✅ comprehension over existing collection
#### range with step

- ✅ iterates with positive step
- ✅ iterates with negative step
#### dictionary comprehension

- ✅ creates dict from range
#### complex loop patterns

- ✅ nested comprehension
- ✅ conditional nesting in comprehension

