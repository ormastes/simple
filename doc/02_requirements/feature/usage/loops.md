# Loop Constructs Specification
*Source:* `test/feature/usage/loops_spec.spl`
**Feature IDs:** #1100  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

The Simple language provides several loop constructs for iterating over collections and
executing code repeatedly. Loop types include while loops for condition-based iteration,
for loops for collection iteration, and comprehensions for creating collections from
iterative expressions. All loops support break and continue flow control.

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

## Feature: Loop Constructs

## Loop Constructs Specification

    This test suite verifies loop functionality including:
    - Basic while loops with conditions
    - For loops over collections and ranges
    - Break and continue flow control
    - Nested loops
    - List and dictionary comprehensions
    - Loop variable scoping and binding

### Scenario: while loops

| # | Example | Status |
|---|---------|--------|
| 1 | executes while loop with condition | pass |
| 2 | exits while loop when condition becomes false | pass |
| 3 | handles while loop with break | pass |
| 4 | handles while loop with continue | pass |

**Example:** executes while loop with condition
    Given var count = 0
    Given var i = 0
    Then  expect count == 5

**Example:** exits while loop when condition becomes false
    Given var total = 0
    Given var i = 1
    Then  expect total == 10

**Example:** handles while loop with break
    Given var i = 0
    Given var count = 0
    Then  expect count == 5

**Example:** handles while loop with continue
    Given var sum = 0
    Given var i = 0
    Then  expect sum == 12

### Scenario: for loops over ranges

| # | Example | Status |
|---|---------|--------|
| 1 | iterates over exclusive range | pass |
| 2 | iterates over inclusive range | pass |
| 3 | handles negative ranges | pass |

**Example:** iterates over exclusive range
    Given var sum = 0
    Then  expect sum == 10

**Example:** iterates over inclusive range
    Given var sum = 0
    Then  expect sum == 15

**Example:** handles negative ranges
    Given var sum = 0
    Then  expect sum == -6

### Scenario: for loops over collections

| # | Example | Status |
|---|---------|--------|
| 1 | iterates over list | pass |
| 2 | iterates with break | pass |
| 3 | iterates with continue | pass |

**Example:** iterates over list
    Given val items = [1, 2, 3, 4, 5]
    Given var sum = 0
    Then  expect sum == 15

**Example:** iterates with break
    Given val items = [1, 2, 3, 4, 5]
    Given var sum = 0
    Then  expect sum == 3

**Example:** iterates with continue
    Given val items = [1, 2, 3, 4, 5]
    Given var sum = 0
    Then  expect sum == 12

### Scenario: nested loops

| # | Example | Status |
|---|---------|--------|
| 1 | executes nested loops | pass |
| 2 | breaks outer loop from nested loop | pass |

**Example:** executes nested loops
    Given var sum = 0
    Then  expect sum == 9

**Example:** breaks outer loop from nested loop
    Given var sum = 0
    Then  expect sum == 6

### Scenario: list comprehensions

| # | Example | Status |
|---|---------|--------|
| 1 | creates list from range | pass |
| 2 | filters with comprehension | pass |
| 3 | transforms and filters | pass |
| 4 | comprehension over existing collection | pass |

**Example:** creates list from range
    Given val result = [for x in 0..5: x * 2]
    Then  expect result == [0, 2, 4, 6, 8]

**Example:** filters with comprehension
    Given val result = [for x in 0..10 if x % 2 == 0: x]
    Then  expect result == [0, 2, 4, 6, 8]

**Example:** transforms and filters
    Given val result = [for x in 1..6 if x > 2: x * 2]
    Then  expect result == [6, 8, 10]

**Example:** comprehension over existing collection
    Given val items = [1, 2, 3, 4, 5]
    Given val result = [for x in items: x * 2]
    Then  expect result == [2, 4, 6, 8, 10]

### Scenario: range with step

| # | Example | Status |
|---|---------|--------|
| 1 | iterates with positive step | pass |
| 2 | iterates with negative step | pass |

**Example:** iterates with positive step
    Given val result = [for x in range(0, 10, 2): x]
    Then  expect result == [0, 2, 4, 6, 8]

**Example:** iterates with negative step
    Given val result = [for x in range(5, 0, -1): x]
    Then  expect result == [5, 4, 3, 2, 1]

### Scenario: dictionary comprehension

| # | Example | Status |
|---|---------|--------|
| 1 | creates dict from range | pass |

**Example:** creates dict from range
    Given val result = {for x in 0..3: (x, x * 2)}
    Then  expect result[0] == 0
    Then  expect result[1] == 2
    Then  expect result[2] == 4

### Scenario: complex loop patterns

| # | Example | Status |
|---|---------|--------|
| 1 | nested comprehension | pass |
| 2 | conditional nesting in comprehension | pass |

**Example:** nested comprehension
    Given val matrix = [[1, 2], [3, 4], [5, 6]]
    Given val result = [for row in matrix: [for cell in row: cell * 2]]
    Then  expect result == [[2, 4], [6, 8], [10, 12]]

**Example:** conditional nesting in comprehension
    Given val result = [for x in 0..5 if x > 1: [for y in 0..2: x + y]]
    Then  expect result.len() == 3


