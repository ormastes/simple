# Collections Specification
*Source:* `test/feature/usage/collections_spec.spl`
**Feature IDs:** #COLLECTIONS-001  |  **Category:** Language | Collections  |  **Status:** Implemented

## Overview



use std.text.{NL}

## Overview

Tests for collection types including arrays, tuples, dictionaries, and strings.
Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## Syntax

```simple
val arr = [1, 2, 3]                    # Array literal
val t = (10, 20, 30)                   # Tuple literal
val d = {"a": 1, "b": 2}               # Dictionary literal
val doubled = arr.map(\x: x * 2)       # Functional method
val squares = [x * x for x in arr]    # List comprehension
val sub = arr[1:4]                     # Slicing
val last = arr[-1]                     # Negative indexing
```

## Feature: Array Basics

## Array Literal and Basic Operations

    Tests for array creation and basic access methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates array literal and accesses by index | pass |
| 2 | gets array length | pass |
| 3 | gets first and last elements | pass |
| 4 | checks if array contains element | pass |
| 5 | checks if array is empty | pass |

**Example:** creates array literal and accesses by index
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[2] == 3

**Example:** gets array length
    Given val arr = [10, 20, 30]
    Then  expect arr.len() == 3

**Example:** gets first and last elements
    Given val arr = [5, 10, 15, 20]
    Then  expect arr.first() + arr.last() == 25

**Example:** checks if array contains element
    Given val arr = [1, 2, 3]
    Given var result = 0
    Then  expect result == 1

**Example:** checks if array is empty
    Given val arr = []
    Given var result = 0
    Then  expect result == 1

## Feature: Tuple Basics

## Tuple Literal and Operations

    Tests for tuple creation and access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates tuple literal and accesses by index | pass |
| 2 | gets tuple length | pass |
| 3 | destructures tuple | pass |

**Example:** creates tuple literal and accesses by index
    Given val t = (10, 20, 30)
    Then  expect t[1] == 20

**Example:** gets tuple length
    Given val t = (1, 2, 3, 4)
    Then  expect t.len() == 4

**Example:** destructures tuple
    Given val (a, b, c) = (10, 20, 30)
    Then  expect a + b + c == 60

## Feature: Dictionary Basics

## Dictionary Literal and Operations

    Tests for dictionary creation and access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates dict literal and accesses by key | pass |
| 2 | gets dict length | pass |
| 3 | checks if dict contains key | pass |
| 4 | gets value from dict | pass |

**Example:** creates dict literal and accesses by key
    Given val d = {"a": 10, "b": 20}
    Then  expect d["a"] + d["b"] == 30

**Example:** gets dict length
    Given val d = {"x": 1, "y": 2, "z": 3}
    Then  expect d.len() == 3

**Example:** checks if dict contains key
    Given val d = {"name": 42}
    Given var result = 0
    Then  expect result == 1

**Example:** gets value from dict
    Given val d = {"value": 99}
    Then  expect d.get("value") == 99

## Feature: String Operations

## String Methods

    Tests for string operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets string length | pass |
| 2 | checks if string contains substring | pass |
| 3 | indexes string to get character | pass |

**Example:** gets string length
    Given val s = "hello"
    Then  expect s.len() == 5

**Example:** checks if string contains substring
    Given val s = "hello world"
    Given var result = 0
    Then  expect result == 1

**Example:** indexes string to get character
    Given val s = "abc"
    Given var result = 0
    Then  expect result == 1

## Feature: Array Mutation Methods

## Array Push, Concat, and Slice

    Tests for array modification operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | pushes element to array | pass |
| 2 | concatenates two arrays | pass |
| 3 | slices array | pass |

**Example:** pushes element to array
    Given var arr = [1, 2, 3]
    Then  expect arr[3] == 4

**Example:** concatenates two arrays
    Given val a = [1, 2]
    Given val b = [3, 4]
    Given val c = a.concat(b)
    Then  expect c.len() == 4

**Example:** slices array
    Given val arr = [0, 1, 2, 3, 4, 5]
    Given val sliced = arr[2:5]
    Then  expect sliced.len() == 3

## Feature: Array Functional Methods

## Map, Filter, Reduce, and Other Functional Operations

    Tests for functional array methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maps array elements | pass |
| 2 | filters array elements | pass |
| 3 | reduces array to single value | pass |
| 4 | checks all elements match predicate | pass |
| 5 | joins array elements to string | pass |
| 6 | sums array elements | pass |
| 7 | reverses array | pass |

**Example:** maps array elements
    Given val arr = [1, 2, 3]
    Given val doubled = arr.map(\x: x * 2)
    Then  expect doubled[1] == 4

**Example:** filters array elements
    Given val arr = [1, 2, 3, 4, 5]
    Given val evens = arr.filter(\x: x % 2 == 0)
    Then  expect evens.len() == 2

**Example:** reduces array to single value
    Given val arr = [1, 2, 3, 4, 5]
    Given val sum = arr.reduce(0, \acc, x: acc + x)
    Then  expect sum == 15

**Example:** checks all elements match predicate
    Given val arr = [2, 4, 6]
    Given val all_even = arr.all(\x: x % 2 == 0)
    Given var result = 0
    Then  expect result == 1

**Example:** joins array elements to string
    Given val arr = [1, 2, 3]
    Given val s = arr.join("-")
    Given var result = 0
    Then  expect result == 1

**Example:** sums array elements
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr.sum() == 15

**Example:** reverses array
    Given var arr = [1, 2, 3]
    Given val rev = arr.reverse()
    Then  expect rev[0] == 3

## Feature: Dictionary Methods

## Dict Set, Remove, Merge, and Get Operations

    Tests for dictionary modification and access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | sets new key in dict | pass |
| 2 | removes key from dict | pass |
| 3 | merges two dicts | pass |
| 4 | gets with default value | pass |

**Example:** sets new key in dict
    Given var d = {"a": 1}
    Then  expect d["b"] == 2

**Example:** removes key from dict
    Given var d = {"a": 1, "b": 2}
    Then  expect d.len() == 1

**Example:** merges two dicts
    Given var d1 = {"a": 1}
    Given val d2 = {"b": 2}
    Given val d = d1.merge(d2)
    Then  expect d.len() == 2

**Example:** gets with default value
    Given val d = {"a": 10}
    Then  expect d.get_or("b", 99) == 99

## Feature: List Comprehension

## List Comprehension Syntax

    Tests for [expr for x in iterable] syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates list with basic comprehension | pass |
| 2 | creates list with condition | pass |
| 3 | creates squares list | pass |

**Example:** creates list with basic comprehension
    Given val arr = [1, 2, 3, 4, 5]
    Given val doubled = [x * 2 for x in arr]
    Then  expect doubled[2] == 6

**Example:** creates list with condition
    Given val arr = [1, 2, 3, 4, 5, 6]
    Given val evens = [x for x in arr if x % 2 == 0]
    Then  expect evens.len() == 3

**Example:** creates squares list
    Given val squares = [x * x for x in [1, 2, 3, 4]]
    Then  expect squares[3] == 16

## Feature: Dict Comprehension

## Dict Comprehension Syntax

    Tests for {key: value for x in iterable} syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates dict with comprehension | pass |

**Example:** creates dict with comprehension
    Given val arr = [1, 2, 3]
    Given val d = {x: x * x for x in arr}
    Then  expect d[2] == 4

## Feature: Slicing

## Array and String Slicing

    Tests for [start:end:step] slice syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | slices with start and end | pass |
| 2 | slices from start index to end | pass |
| 3 | slices from beginning to end index | pass |
| 4 | slices with step | pass |

**Example:** slices with start and end
    Given val arr = [0, 1, 2, 3, 4, 5]
    Given val sub = arr[1:4]
    Then  expect sub.len() == 3

**Example:** slices from start index to end
    Given val arr = [0, 1, 2, 3, 4]
    Given val sub = arr[2:]
    Then  expect sub[0] == 2

**Example:** slices from beginning to end index
    Given val arr = [0, 1, 2, 3, 4]
    Given val sub = arr[:3]
    Then  expect sub.len() == 3

**Example:** slices with step
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7]
    Given val evens = arr[::2]
    Then  expect evens.len() == 4

## Feature: Negative Indexing

## Negative Index Access

    Tests for arr[-1] style negative indexing.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accesses last element with -1 | pass |
| 2 | accesses second from end with -2 | pass |
| 3 | accesses string with negative index | pass |

**Example:** accesses last element with -1
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[-1] == 50

**Example:** accesses second from end with -2
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[-2] == 4

**Example:** accesses string with negative index
    Given val s = "hello"
    Given val c = s[-1]
    Given var result = 0
    Then  expect result == 1

## Feature: Spread Operators

## Array Spread Syntax

    Tests for [*a, *b] spread operator.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | spreads two arrays | pass |
| 2 | spreads with mixed elements | pass |

**Example:** spreads two arrays
    Given val a = [1, 2, 3]
    Given val b = [4, 5]
    Given val c = [*a, *b]
    Then  expect c.len() == 5

**Example:** spreads with mixed elements
    Given val a = [2, 3]
    Given val arr = [1, *a, 4]
    Then  expect arr[2] == 3

## Feature: Tuple Unpacking

## Tuple Destructuring Assignment

    Tests for let (a, b) = tuple syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | unpacks basic tuple | pass |
| 2 | unpacks with swap pattern | pass |
| 3 | unpacks array to tuple | pass |

**Example:** unpacks basic tuple
    Given val (x, y) = (1, 2)
    Then  expect x + y == 3

**Example:** unpacks with swap pattern
    Given val a = 10
    Given val b = 20
    Given val (x, y) = (b, a)
    Then  expect x == 20

**Example:** unpacks array to tuple
    Given val arr = [5, 10, 15]
    Given val (first, second, third) = arr
    Then  expect second == 10

## Feature: Chained Comparisons

## Python-style Chained Comparisons

    Tests for a < x < b style comparisons.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates basic chained comparison | pass |
| 2 | evaluates false chained comparison | pass |
| 3 | evaluates three-way comparison | pass |
| 4 | evaluates mixed comparison operators | pass |

**Example:** evaluates basic chained comparison
    Given val x = 5
    Given var result = 0
    Then  expect result == 1

**Example:** evaluates false chained comparison
    Given val x = 15
    Given var result = 0
    Then  expect result == 0

**Example:** evaluates three-way comparison
    Given val a = 1
    Given val b = 5
    Given val c = 10
    Given var result = 0
    Then  expect result == 1

**Example:** evaluates mixed comparison operators
    Given val x = 5
    Given var result = 0
    Then  expect result == 1

## Feature: Context Managers

## With Statement

    Tests for with statement context managers.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | executes basic with block | pass |
| 2 | binds resource with as | pass |
| 3 | calls __enter__ and __exit__ on class | pass |

**Example:** executes basic with block
    Given var counter = 0
    Then  expect counter == 1

**Example:** binds resource with as
    Given val value = x + 1
    Then  expect value == 43

**Example:** calls __enter__ and __exit__ on class
    Given val r = Resource(value: 5)
    Given val ret_value = v
    Then  expect ret_value == 15

## Feature: Decorators

## Function Decorators

    Tests for @decorator syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | applies basic decorator | pass |
| 2 | applies decorator with arguments | pass |

**Example:** applies basic decorator
    Then  expect add_one(5) == 12

**Example:** applies decorator with arguments
    Then  expect increment(10) == 33


