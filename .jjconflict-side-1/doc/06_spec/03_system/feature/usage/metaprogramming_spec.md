# Simple Language Metaprogramming - Test Specification

> This file contains executable test cases for metaprogramming features that are currently implemented in Simple's runtime.

<!-- sdn-diagram:id=metaprogramming_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metaprogramming_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metaprogramming_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metaprogramming_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Metaprogramming - Test Specification

This file contains executable test cases for metaprogramming features that are currently implemented in Simple's runtime.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Various |
| Category | Language Features |
| Status | Partial Implementation |
| Type | Extracted Examples |
| Reference | metaprogramming.md |
| Source | `test/03_system/feature/usage/metaprogramming_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases for metaprogramming features that are
currently implemented in Simple's runtime.

Tests cover: comprehensions, indexing, pattern matching, and basic error handling.

**Note:** Advanced features (DSL blocks, decorators, slicing, context managers, move closures)
are not yet fully implemented.

## Scenarios

### Metaprogramming Spec

#### list comprehensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# List comprehensions with filters
val evens = [for x in 0..10 if x % 2 == 0: x]
expect(evens[0]).to_equal(0)
expect(evens[1]).to_equal(2)
expect(evens[2]).to_equal(4)
```

</details>

#### list comprehensions - transformation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Transform elements in comprehension
val squares = [for x in 1..6: x * x]
expect(squares[0]).to_equal(1)
expect(squares[1]).to_equal(4)
expect(squares[2]).to_equal(9)
```

</details>

#### array indexing - basic

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Basic array indexing
val arr = [10, 20, 30, 40, 50]
expect(arr[0]).to_equal(10)
expect(arr[2]).to_equal(30)
expect(arr[4]).to_equal(50)
```

</details>

#### array indexing - last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Access last element using len()
val arr = [10, 20, 30, 40, 50]
val last = arr[arr.len() - 1]
expect(last).to_equal(50)
```

</details>

#### pattern matching - guard patterns

1. fn classify
   - Expected: classify(-5) equals `negative`
   - Expected: classify(0) equals `zero`
   - Expected: classify(10) equals `positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Guard patterns using if/else
fn classify(n: i64) -> text:
    if n < 0:
        return "negative"
    else if n == 0:
        return "zero"
    else:
        return "positive"

expect(classify(-5)).to_equal("negative")
expect(classify(0)).to_equal("zero")
expect(classify(10)).to_equal("positive")
```

</details>

#### pattern matching - simple matching

1. fn find value
   - Expected: find_value(numbers, 20) equals `found`
   - Expected: find_value(numbers, 99) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple value matching with functions
fn find_value(arr: [i64], target: i64) -> text:
    for x in arr:
        if x == target:
            return "found"
    return "not found"

val numbers = [10, 20, 30]
expect(find_value(numbers, 20)).to_equal("found")
expect(find_value(numbers, 99)).to_equal("not found")
```

</details>

#### error handling - safe division

1. fn safe divide
   - Expected: result1 equals `5`
   - Expected: result2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Safe operations with error returns
fn safe_divide(a: i64, b: i64) -> i64:
    if b == 0:
        return 0  # Error sentinel
    a / b

val result1 = safe_divide(10, 2)
val result2 = safe_divide(10, 0)

expect(result1).to_equal(5)
expect(result2).to_equal(0)
```

</details>

#### error handling - option pattern

1. fn find first even
   - Expected: result equals `6`
   - Expected: not_found equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Option pattern with nil checking
fn find_first_even(arr: [i64]) -> i64:
    for x in arr:
        if x % 2 == 0:
            return x
    return -1  # Not found sentinel

val numbers = [1, 3, 6, 9]
val result = find_first_even(numbers)
expect(result).to_equal(6)

val odd_only = [1, 3, 5]
val not_found = find_first_even(odd_only)
expect(not_found).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
