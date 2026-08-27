# Collections Specification

> Tests for collection types including arrays, tuples, dictionaries, and strings. Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for collection types including arrays, tuples, dictionaries, and strings.
Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## Syntax

```simple
var arr = [1, 2, 3]                    # Array literal
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates array literal and accesses by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates array literal and accesses by index")
var arr = [1, 2, 3, 4, 5]
expect arr[2] == 3
```

</details>

#### gets array length

- gets array length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets array length")
var arr = [10, 20, 30]
expect arr.len() == 3
```

</details>

#### gets first and last elements

- gets first and last elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets first and last elements")
var arr = [5, 10, 15, 20]
expect arr.first() + arr.last() == 25
```

</details>

#### checks if array contains element

- checks if array contains element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if array contains element")
var arr = [1, 2, 3]
var result = 0
if arr.contains(2):
    result = 1
expect result == 1
```

</details>

#### checks if array is empty

- checks if array is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if array is empty")
var arr = []
var result = 0
if arr.is_empty():
    result = 1
expect result == 1
```

</details>

### Tuple Basics

#### creates tuple literal and accesses by index

- creates tuple literal and accesses by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates tuple literal and accesses by index")
val t = (10, 20, 30)
expect t[1] == 20
```

</details>

#### gets tuple length

- gets tuple length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets tuple length")
val t = (1, 2, 3, 4)
expect t.len() == 4
```

</details>

#### destructures tuple

- destructures tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures tuple")
val _tuple = (10, 20, 30)
val a = _tuple[0]
val b = _tuple[1]
val c = _tuple[2]
expect a + b + c == 60
```

</details>

### Dictionary Basics

#### creates dict literal and accesses by key

- creates dict literal and accesses by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dict literal and accesses by key")
val d = {"a": 10, "b": 20}
expect d["a"] + d["b"] == 30
```

</details>

#### gets dict length

- gets dict length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets dict length")
val d = {"x": 1, "y": 2, "z": 3}
expect d.len() == 3
```

</details>

#### checks if dict contains key

- checks if dict contains key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if dict contains key")
val d = {"name": 42}
var result = 0
if d.has("name"):
    result = 1
expect result == 1
```

</details>

#### gets value from dict

- gets value from dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets value from dict")
val d = {"value": 99}
expect d.get("value") == 99
```

</details>

### String Operations

#### gets string length

- gets string length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets string length")
val s = "hello"
expect s.len() == 5
```

</details>

#### checks if string contains substring

- checks if string contains substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if string contains substring")
val s = "hello world"
var result = 0
if s.contains("world"):
    result = 1
expect result == 1
```

</details>

#### indexes string to get character

- indexes string to get character


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("indexes string to get character")
val s = "abc"
var result = 0
if s[1] == "b":
    result = 1
expect result == 1
```

</details>

### Array Mutation Methods

#### pushes element to array

- pushes element to array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pushes element to array")
var arr = [1, 2, 3]
arr = arr.push(4)
expect arr[3] == 4
```

</details>

#### concatenates two arrays

- concatenates two arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concatenates two arrays")
val a = [1, 2]
val b = [3, 4]
val c = a.concat(b)
expect c.len() == 4
```

</details>

#### slices array

- slices array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices array")
var arr = [0, 1, 2, 3, 4, 5]
val sliced = arr[2:5]
expect sliced.len() == 3
```

</details>

### Array Functional Methods

#### maps array elements

- maps array elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps array elements")
var arr = [1, 2, 3]
val doubled = arr.map(_ * 2)
expect doubled[1] == 4
```

</details>

#### filters array elements

- filters array elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters array elements")
var arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect evens.len() == 2
```

</details>

#### reduces array to single value

- reduces array to single value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reduces array to single value")
var arr = [1, 2, 3, 4, 5]
val sum = arr.reduce(0, \acc, x: acc + x)
expect sum == 15
```

</details>

#### checks all elements match predicate

- checks all elements match predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks all elements match predicate")
var arr = [2, 4, 6]
val all_even = arr.all(_1 % 2 == 0)
var result = 0
if all_even:
    result = 1
expect result == 1
```

</details>

#### joins array elements to string

- joins array elements to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("joins array elements to string")
var arr = [1, 2, 3]
val s = arr.join("-")
var result = 0
if s == "1-2-3":
    result = 1
expect result == 1
```

</details>

#### sums array elements

- sums array elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sums array elements")
var arr = [1, 2, 3, 4, 5]
expect arr.sum() == 15
```

</details>

#### reverses array

- reverses array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverses array")
var arr = [1, 2, 3]
val rev = arr.reverse()
expect rev[0] == 3
```

</details>

### Dictionary Methods

#### sets new key in dict

- sets new key in dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets new key in dict")
var d = {"a": 1}
d = d.set("b", 2)
expect d["b"] == 2
```

</details>

#### removes key from dict

- removes key from dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes key from dict")
var d = {"a": 1, "b": 2}
d = d.remove("a")
expect d.len() == 1
```

</details>

#### merges two dicts

- merges two dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges two dicts")
var d1 = {"a": 1}
val d2 = {"b": 2}
val d = d1.merge(d2)
expect d.len() == 2
```

</details>

#### gets with default value

- gets with default value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets with default value")
val d = {"a": 10}
expect d.get_or("b", 99) == 99
```

</details>

### List Comprehension

#### creates list with basic comprehension

- creates list with basic comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list with basic comprehension")
var arr = [1, 2, 3, 4, 5]
val doubled = [x * 2 for x in arr]
expect doubled[2] == 6
```

</details>

#### creates list with condition

- creates list with condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list with condition")
var arr = [1, 2, 3, 4, 5, 6]
val evens = [x for x in arr if x % 2 == 0]
expect evens.len() == 3
```

</details>

#### creates squares list

- creates squares list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates squares list")
val squares = [x * x for x in [1, 2, 3, 4]]
expect squares[3] == 16
```

</details>

### Dict Comprehension

#### creates dict with comprehension

- creates dict with comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dict with comprehension")
var arr = [1, 2, 3]
val d = {x: x * x for x in arr}
expect d[2] == 4
```

</details>

### Slicing

#### slices with start and end

- slices with start and end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with start and end")
var arr = [0, 1, 2, 3, 4, 5]
val sub = arr[1:4]
expect sub.len() == 3
```

</details>

#### slices from start index to end

- slices from start index to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices from start index to end")
var arr = [0, 1, 2, 3, 4]
val sub = arr[2:]
expect sub[0] == 2
```

</details>

#### slices from beginning to end index

- slices from beginning to end index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices from beginning to end index")
var arr = [0, 1, 2, 3, 4]
val sub = arr[:3]
expect sub.len() == 3
```

</details>

#### slices with step

- slices with step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices with step")
var arr = [0, 1, 2, 3, 4, 5, 6, 7]
val evens = arr[::2]
expect evens.len() == 4
```

</details>

### Negative Indexing

#### accesses last element with -1

- accesses last element with -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses last element with -1")
var arr = [10, 20, 30, 40, 50]
expect arr[-1] == 50
```

</details>

#### accesses second from end with -2

- accesses second from end with -2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses second from end with -2")
var arr = [1, 2, 3, 4, 5]
expect arr[-2] == 4
```

</details>

#### accesses string with negative index

- accesses string with negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses string with negative index")
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

- spreads two arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spreads two arrays")
val a = [1, 2, 3]
val b = [4, 5]
val c = [*a, *b]
expect c.len() == 5
```

</details>

#### spreads with mixed elements

- spreads with mixed elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spreads with mixed elements")
val a = [2, 3]
var arr = [1, *a, 4]
expect arr[2] == 3
```

</details>

### Tuple Unpacking

#### unpacks basic tuple

- unpacks basic tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unpacks basic tuple")
val _pair = (1, 2)
val x = _pair[0]
val y = _pair[1]
expect x + y == 3
```

</details>

#### unpacks with swap pattern

- unpacks with swap pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unpacks with swap pattern")
val a = 10
val b = 20
val _swap = (b, a)
val x = _swap[0]
val y = _swap[1]
expect x == 20
```

</details>

#### unpacks array to tuple

- unpacks array to tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unpacks array to tuple")
var arr = [5, 10, 15]
val first = arr[0]
val second = arr[1]
val third = arr[2]
expect second == 10
```

</details>

### Chained Comparisons

#### evaluates basic chained comparison

- evaluates basic chained comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates basic chained comparison")
val x = 5
var result = 0
if 0 < x < 10:
    result = 1
expect result == 1
```

</details>

#### evaluates false chained comparison

- evaluates false chained comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates false chained comparison")
val x = 15
var result = 0
if 0 < x < 10:
    result = 1
expect result == 0
```

</details>

#### evaluates three-way comparison

- evaluates three-way comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates three-way comparison")
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

- evaluates mixed comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates mixed comparison operators")
val x = 5
var result = 0
if 0 <= x <= 10:
    result = 1
expect result == 1
```

</details>

### Context Managers

#### executes basic with block

- executes basic with block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes basic with block")
var counter = 0
with 42:
    counter = 1
expect counter == 1
```

</details>

#### binds resource with as

- binds resource with as


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds resource with as")
with 42 as x:
    val value = x + 1
expect value == 43
```

</details>

#### calls __enter__ and __exit__ on class

- calls __enter__ and __exit__ on class


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls __enter__ and __exit__ on class")
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

- applies basic decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies basic decorator")
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

- applies decorator with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies decorator with arguments")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `187da163c414b8aaddfd3aa600e66eb1c098e0715d803e4c8d22c15b8c2929d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `187da163c414b8aaddfd3aa600e66eb1c098e0715d803e4c8d22c15b8c2929d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `187da163c414b8aaddfd3aa600e66eb1c098e0715d803e4c8d22c15b8c2929d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/collections_spec.spl
mirror: doc/06_spec/03_system/feature/usage/collections_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/collections_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/collections_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/collections_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates array literal and accesses by index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/collections_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets array length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/collections_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets first and last elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
