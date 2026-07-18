# Collections Specification

> Tests for collection types including arrays, tuples, dictionaries, and strings. Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

<!-- sdn-diagram:id=collections_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collections_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collections_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collections_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections Specification

Tests for collection types including arrays, tuples, dictionaries, and strings. Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLLECTIONS-001 |
| Category | Language \| Collections |
| Status | Implemented |
| Source | `test/03_system/feature/usage/collections_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for collection types including arrays, tuples, dictionaries, and strings.
Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## Syntax

```simple
var arr = [1, 2, 3]                    # Array literal
val t = (10, 20, 30)                   # Tuple literal
val d = {"a": 1, "b": 2}               # Dictionary literal
val doubled = arr.map(_1 * 2)          # Functional method
val squares = [x * x for x in arr]    # List comprehension
val sub = arr[1:4]                     # Slicing
val last = arr[-1]                     # Negative indexing
```

## Scenarios

### Array Basics

#### creates array literal and accesses by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr[2] == 3
```

</details>

#### gets array length

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30]
expect arr.len() == 3
```

</details>

#### gets first and last elements

1. expect arr first


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [5, 10, 15, 20]
expect arr.first() + arr.last() == 25
```

</details>

#### checks if array contains element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
var result = 0
if arr.contains(2):
    result = 1
expect result == 1
```

</details>

#### checks if array is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
var result = 0
if arr.is_empty():
    result = 1
expect result == 1
```

</details>

### Tuple Basics

#### creates tuple literal and accesses by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 20, 30)
expect t[1] == 20
```

</details>

#### gets tuple length

1. expect t len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2, 3, 4)
expect t.len() == 4
```

</details>

#### destructures tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _tuple = (10, 20, 30)
val a = _tuple[0]
val b = _tuple[1]
val c = _tuple[2]
expect a + b + c == 60
```

</details>

### Dictionary Basics

#### creates dict literal and accesses by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 10, "b": 20}
expect d["a"] + d["b"] == 30
```

</details>

#### gets dict length

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"x": 1, "y": 2, "z": 3}
expect d.len() == 3
```

</details>

#### checks if dict contains key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"name": 42}
var result = 0
if d.has("name"):
    result = 1
expect result == 1
```

</details>

#### gets value from dict

1. expect d get


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"value": 99}
expect d.get("value") == 99
```

</details>

### String Operations

#### gets string length

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s.len() == 5
```

</details>

#### checks if string contains substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
var result = 0
if s.contains("world"):
    result = 1
expect result == 1
```

</details>

#### indexes string to get character

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
var result = 0
if s[1] == "b":
    result = 1
expect result == 1
```

</details>

### Array Mutation Methods

#### pushes element to array

1. arr = arr push


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr = arr.push(4)
expect arr[3] == 4
```

</details>

#### concatenates two arrays

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2]
val b = [3, 4]
val c = a.concat(b)
expect c.len() == 4
```

</details>

#### slices array

1. expect sliced len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4, 5]
val sliced = arr[2:5]
expect sliced.len() == 3
```

</details>

### Array Functional Methods

#### maps array elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val doubled = arr.map(_ * 2)
expect doubled[1] == 4
```

</details>

#### filters array elements

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect evens.len() == 2
```

</details>

#### reduces array to single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val sum = arr.reduce(0, \acc, x: acc + x)
expect sum == 15
```

</details>

#### checks all elements match predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [2, 4, 6]
val all_even = arr.all(_1 % 2 == 0)
var result = 0
if all_even:
    result = 1
expect result == 1
```

</details>

#### joins array elements to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val s = arr.join("-")
var result = 0
if s == "1-2-3":
    result = 1
expect result == 1
```

</details>

#### sums array elements

1. expect arr sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr.sum() == 15
```

</details>

#### reverses array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val rev = arr.reverse()
expect rev[0] == 3
```

</details>

### Dictionary Methods

#### sets new key in dict

1. d = d set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"a": 1}
d = d.set("b", 2)
expect d["b"] == 2
```

</details>

#### removes key from dict

1. d = d remove
2. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"a": 1, "b": 2}
d = d.remove("a")
expect d.len() == 1
```

</details>

#### merges two dicts

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d1 = {"a": 1}
val d2 = {"b": 2}
val d = d1.merge(d2)
expect d.len() == 2
```

</details>

#### gets with default value

1. expect d get or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 10}
expect d.get_or("b", 99) == 99
```

</details>

### List Comprehension

#### creates list with basic comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val doubled = [x * 2 for x in arr]
expect doubled[2] == 6
```

</details>

#### creates list with condition

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5, 6]
val evens = [x for x in arr if x % 2 == 0]
expect evens.len() == 3
```

</details>

#### creates squares list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val squares = [x * x for x in [1, 2, 3, 4]]
expect squares[3] == 16
```

</details>

### Dict Comprehension

#### creates dict with comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val d = {x: x * x for x in arr}
expect d[2] == 4
```

</details>

### Slicing

#### slices with start and end

1. expect sub len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4, 5]
val sub = arr[1:4]
expect sub.len() == 3
```

</details>

#### slices from start index to end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4]
val sub = arr[2:]
expect sub[0] == 2
```

</details>

#### slices from beginning to end index

1. expect sub len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4]
val sub = arr[:3]
expect sub.len() == 3
```

</details>

#### slices with step

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4, 5, 6, 7]
val evens = arr[::2]
expect evens.len() == 4
```

</details>

### Negative Indexing

#### accesses last element with -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30, 40, 50]
expect arr[-1] == 50
```

</details>

#### accesses second from end with -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr[-2] == 4
```

</details>

#### accesses string with negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val c = s[-1]
var result = 0
if c == "o":
    result = 1
expect result == 1
```

</details>

### Spread Operators

#### spreads two arrays

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [4, 5]
val c = [*a, *b]
expect c.len() == 5
```

</details>

#### spreads with mixed elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [2, 3]
var arr = [1, *a, 4]
expect arr[2] == 3
```

</details>

### Tuple Unpacking

#### unpacks basic tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _pair = (1, 2)
val x = _pair[0]
val y = _pair[1]
expect x + y == 3
```

</details>

#### unpacks with swap pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val _swap = (b, a)
val x = _swap[0]
val y = _swap[1]
expect x == 20
```

</details>

#### unpacks array to tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [5, 10, 15]
val first = arr[0]
val second = arr[1]
val third = arr[2]
expect second == 10
```

</details>

### Chained Comparisons

#### evaluates basic chained comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
var result = 0
if 0 < x < 10:
    result = 1
expect result == 1
```

</details>

#### evaluates false chained comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 15
var result = 0
if 0 < x < 10:
    result = 1
expect result == 0
```

</details>

#### evaluates three-way comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 5
val c = 10
var result = 0
if a < b < c:
    result = 1
expect result == 1
```

</details>

#### evaluates mixed comparison operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
var result = 0
if 0 <= x <= 10:
    result = 1
expect result == 1
```

</details>

### Context Managers

#### executes basic with block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
with 42:
    counter = 1
expect counter == 1
```

</details>

#### binds resource with as

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
with 42 as x:
    val value = x + 1
expect value == 43
```

</details>

#### calls __enter__ and __exit__ on class

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    value: i64 = 0

    fn __enter__(self):
        return self.value + 10

    fn __exit__(self):
        return 0

val r = Resource(value: 5)
with r as v:
    val ret_value = v
expect ret_value == 15
```

</details>

### Decorators

#### applies basic decorator

1. fn double result
2. fn wrapper
3. fn add one
4. expect add one


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_result(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@double_result
fn add_one(x):
    return x + 1

expect add_one(5) == 12
```

</details>

#### applies decorator with arguments

1. fn multiply by
2. fn decorator
3. fn wrapper
4. fn increment
5. expect increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply_by(factor):
    fn decorator(f):
        fn wrapper(x):
            return f(x) * factor
        return wrapper
    return decorator

@multiply_by(3)
fn increment(x):
    return x + 1

expect increment(10) == 33
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
