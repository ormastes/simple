# Collection Utilities Specification
*Source:* `test/feature/usage/collection_utilities_spec.spl`
**Feature IDs:** #COLL-UTIL-001 to #COLL-UTIL-052  |  **Category:** Runtime | Collections  |  **Status:** Implemented

## Overview



use std.text.{NL}

Tests collection utility functions including:
- Array sorting and reversing
- Array aggregation (sum, min, max, count)
- Array transformation (zip, enumerate, flatten, unique)
- Array slicing (take, drop)
- Array predicates (all_truthy, any_truthy)
- Tuple operations
- String operations
- Dictionary operations

## Array Utility Methods

```simple
# Sorting (returns new array)
val sorted = arr.sort()      # Returns new sorted array
val sorted = arr.sorted()    # Alias for sort

# Reversing (returns new array)
val rev = arr.reverse()      # Returns new reversed array
val rev = arr.reversed()     # Alias for reverse

# Access
arr.first()             # First element or nil
arr.last()              # Last element or nil
arr.index_of(value)     # Index or -1 if not found

# Aggregation
arr.sum()               # Sum of numeric elements
arr.min()               # Minimum value or nil
arr.max()               # Maximum value or nil
arr.count_of(value)     # Count occurrences of specific value

# Transformation
arr.concat(other)       # Concatenate arrays
arr.copy()              # Shallow copy
arr.zip(other)          # Zip into tuples
arr.enumerate()         # Add indices as tuples
arr.flatten()           # Flatten nested arrays
arr.unique()            # Remove duplicates
arr.take(n)             # First n elements
arr.drop(n)             # Skip first n elements

# Predicates
arr.all_truthy()        # All elements truthy?
arr.any_truthy()        # Any element truthy?
```

## Feature: Array Sorting

## Sorting Returns New Array

    Tests sort() and sorted() methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | sort returns new sorted array | pass |
| 2 | sorted returns new sorted array | pass |

**Example:** sort returns new sorted array
    Given val arr = [3, 1, 4, 1, 5]
    Given val s = arr.sort()
    Then  expect s[0] == 1
    Then  expect s[1] == 1
    Then  expect s[2] == 3
    Then  expect s[3] == 4
    Then  expect s[4] == 5

**Example:** sorted returns new sorted array
    Given val arr = [3, 1, 2]
    Given val s = arr.sorted()
    Then  expect arr[0] == 3
    Then  expect s[0] == 1
    Then  expect s[1] == 2
    Then  expect s[2] == 3

## Feature: Array Reversing

## Reversing Returns New Array

    Tests reverse() and reversed() methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | reverse returns new reversed array | pass |
| 2 | reversed returns new reversed array | pass |

**Example:** reverse returns new reversed array
    Given val arr = [1, 2, 3]
    Given val r = arr.reverse()
    Then  expect r[0] == 3
    Then  expect r[1] == 2
    Then  expect r[2] == 1

**Example:** reversed returns new reversed array
    Given val arr = [1, 2, 3]
    Given val r = arr.reversed()
    Then  expect arr[0] == 1
    Then  expect r[0] == 3
    Then  expect r[1] == 2
    Then  expect r[2] == 1

## Feature: Array Access Methods

## First, Last, Index Lookup

    Tests array element access methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | first returns first element | pass |
| 2 | last returns last element | pass |
| 3 | first returns nil for empty array | pass |
| 4 | last returns nil for empty array | pass |
| 5 | index_of finds element | pass |
| 6 | index_of returns -1 when not found | pass |

**Example:** first returns first element
    Given val arr = [10, 20, 30]
    Then  expect arr.first() == 10

**Example:** last returns last element
    Given val arr = [10, 20, 30]
    Then  expect arr.last() == 30

**Example:** first returns nil for empty array
    Given val arr: [i64] = []
    Then  expect arr.first() == nil

**Example:** last returns nil for empty array
    Given val arr: [i64] = []
    Then  expect arr.last() == nil

**Example:** index_of finds element
    Given val arr = [10, 20, 30, 20]
    Then  expect arr.index_of(20) == 1  # First occurrence

**Example:** index_of returns -1 when not found
    Given val arr = [10, 20, 30]
    Then  expect arr.index_of(99) == -1

## Feature: Array Concatenation and Copy

## Combining and Duplicating Arrays

    Tests concat() and copy() methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | concatenates two arrays | pass |
| 2 | creates shallow copy | pass |

**Example:** concatenates two arrays
    Given val a = [1, 2]
    Given val b = [3, 4]
    Given val c = a.concat(b)
    Then  expect c.len() == 4
    Then  expect c[0] == 1
    Then  expect c[2] == 3
    Then  expect c[3] == 4

**Example:** creates shallow copy
    Given val arr = [1, 2, 3]
    Given val c = arr.copy()
    Then  expect c.len() == 3
    Then  expect c[0] == 1
    Then  expect c[1] == 2
    Then  expect c[2] == 3

## Feature: Array Aggregation

## Sum, Min, Max, Count

    Tests numeric aggregation methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | sums numeric array | pass |
| 2 | sum of empty array is zero | pass |
| 3 | finds minimum value | pass |
| 4 | finds maximum value | pass |
| 5 | min of empty array is nil | pass |
| 6 | max of empty array is nil | pass |
| 7 | counts occurrences | pass |

**Example:** sums numeric array
    Given val arr = [1, 2, 3, 4]
    Then  expect arr.sum() == 10

**Example:** sum of empty array is zero
    Given val arr: [i64] = []
    Then  expect arr.sum() == 0

**Example:** finds minimum value
    Given val arr = [3, 1, 4, 1, 5]
    Then  expect arr.min() == 1

**Example:** finds maximum value
    Given val arr = [3, 1, 4, 1, 5]
    Then  expect arr.max() == 5

**Example:** min of empty array is nil
    Given val arr: [i64] = []
    Then  expect arr.min() == nil

**Example:** max of empty array is nil
    Given val arr: [i64] = []
    Then  expect arr.max() == nil

**Example:** counts occurrences
    Given val arr = [1, 2, 1, 3, 1]
    Then  expect arr.count_of(1) == 3
    Then  expect arr.count_of(2) == 1
    Then  expect arr.count_of(99) == 0

## Feature: Array Transformation

## Zip, Enumerate, Flatten, Unique

    Tests array transformation methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | zips two arrays into tuples | pass |
| 2 | enumerates array with indices | pass |
| 3 | flattens nested arrays | pass |
| 4 | removes duplicates | pass |

**Example:** zips two arrays into tuples
    Given val a = [1, 2, 3]
    Given val b = [10, 20, 30]
    Given val z = a.zip(b)
    Then  expect z.len() == 3
    Then  expect z[0] == (1, 10)
    Then  expect z[1] == (2, 20)
    Then  expect z[2] == (3, 30)

**Example:** enumerates array with indices
    Given val arr = [10, 20, 30]
    Given val e = arr.enumerate()
    Then  expect e.len() == 3
    Then  expect e[0] == (0, 10)
    Then  expect e[1] == (1, 20)
    Then  expect e[2] == (2, 30)

**Example:** flattens nested arrays
    Given val nested = [[1, 2], [3, 4], [5]]
    Given val result = nested.flatten()
    Then  expect result.len() == 5
    Then  expect result[0] == 1
    Then  expect result[2] == 3
    Then  expect result[4] == 5

**Example:** removes duplicates
    Given val arr = [1, 2, 1, 3, 2, 1]
    Given val u = arr.unique()
    Then  expect u.len() == 3
    Then  expect u[0] == 1
    Then  expect u[1] == 2
    Then  expect u[2] == 3

## Feature: Array Slicing Methods

## Take and Drop

    Tests take() and drop() methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | takes first n elements | pass |
| 2 | drops first n elements | pass |

**Example:** takes first n elements
    Given val arr = [1, 2, 3, 4, 5]
    Given val t = arr.take(3)
    Then  expect t.len() == 3
    Then  expect t[0] == 1
    Then  expect t[2] == 3

**Example:** drops first n elements
    Given val arr = [1, 2, 3, 4, 5]
    Given val d = arr.drop(2)
    Then  expect d.len() == 3
    Then  expect d[0] == 3
    Then  expect d[2] == 5

## Feature: Array Predicates

## All and Any Truthy

    Tests array truthiness predicates.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | all_truthy returns true when all truthy | pass |
| 2 | all_truthy returns false with zero | pass |
| 3 | any_truthy returns true with some truthy | pass |
| 4 | any_truthy returns false when all zero | pass |

**Example:** all_truthy returns true when all truthy
    Given val arr = [1, 2, 3]
    Then  expect arr.all_truthy()

**Example:** all_truthy returns false with zero
    Given val arr = [1, 0, 3]
    Then  expect not arr.all_truthy()

**Example:** any_truthy returns true with some truthy
    Given val arr = [0, 0, 1]
    Then  expect arr.any_truthy()

**Example:** any_truthy returns false when all zero
    Given val arr = [0, 0, 0]
    Then  expect not arr.any_truthy()

## Feature: Array Fill

## Fill Array

    Tests fill() method.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | fills array with value | pass |

**Example:** fills array with value
    Given val arr = [1, 2, 3]
    Given val filled = arr.fill(0)
    Then  expect filled.len() == 3
    Then  expect filled[0] == 0
    Then  expect filled[1] == 0
    Then  expect filled[2] == 0

## Feature: Tuple Operations

## Tuple Creation and Access

    Tests tuple functionality.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates tuple with specified size | pass |
| 2 | gets tuple elements by index | pass |
| 3 | first and last on tuple | pass |

**Example:** creates tuple with specified size
    Given val t = (10, 20, 30)
    Then  expect t.len() == 3

**Example:** gets tuple elements by index
    Given val t = (10, 20, 30)
    Then  expect t[0] == 10
    Then  expect t[1] == 20
    Then  expect t[2] == 30

**Example:** first and last on tuple
    Given val t = (10, 20, 30)
    Then  expect t.first() == 10
    Then  expect t.last() == 30

## Feature: String Operations

## String Creation and Manipulation

    Tests string functionality.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates string and gets length | pass |
| 2 | concatenates strings | pass |
| 3 | handles empty string | pass |

**Example:** creates string and gets length
    Given val s = "Hello, World!"
    Then  expect s.len() == 13

**Example:** concatenates strings
    Given val a = "Hello"
    Given val b = " World"
    Given val c = a + b
    Then  expect c == "Hello World"
    Then  expect c.len() == 11

**Example:** handles empty string
    Given val s = ""
    Then  expect s.len() == 0

## Feature: Dictionary Operations

## Dictionary Creation and Manipulation

    Tests dictionary functionality.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates empty dict | pass |
| 2 | sets and gets values | pass |
| 3 | overwrites existing key | pass |
| 4 | returns nil for missing key | pass |

**Example:** creates empty dict
    Given val d = {}
    Then  expect d.len() == 0

**Example:** sets and gets values
    Given var d = {}
    Then  expect d.len() == 2
    Then  expect d["age"] == 30

**Example:** overwrites existing key
    Given var d = {"counter": 1}
    Then  expect d.len() == 1
    Then  expect d["counter"] == 2

**Example:** returns nil for missing key
    Given val d = {"a": 1}
    Then  expect d["missing"] == nil


