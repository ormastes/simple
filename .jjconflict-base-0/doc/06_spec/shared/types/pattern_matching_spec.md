# Pattern Matching Specification

> 1. expect match int

<!-- sdn-diagram:id=pattern_matching_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_matching_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_matching_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_matching_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 79 | 79 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Matching Specification

## Scenarios

### Pattern Matching

### literal patterns

#### integer literals

#### matches zero

1. expect match int


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_int(0) == "zero"
```

</details>

#### matches positive integers

1. expect match int


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_int(42) == "found"
```

</details>

#### matches larger integers

1. expect match int


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_int(100) == "hundred"
```

</details>

#### uses wildcard for unmatched

1. expect match int


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_int(999) == "other"
```

</details>

#### boolean literals

#### matches true

1. expect match bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_bool(true) == "yes"
```

</details>

#### matches false

1. expect match bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_bool(false) == "no"
```

</details>

#### string literals

#### matches string values

1. expect match string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_string("hello") == "greeting"
```

</details>

#### matches empty string

1. expect match string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_string("") == "empty"
```

</details>

#### uses wildcard for unmatched strings

1. expect match string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_string("other") == "unknown"
```

</details>

### variable binding patterns

#### simple binding

#### binds value to variable

1. expect double via match


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect double_via_match(42) == 84
```

</details>

#### binds and uses in expression

1. expect add five via match


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect add_five_via_match(10) == 15
```

</details>

### wildcard pattern

#### basic wildcards

#### matches anything

1. expect wildcard match


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect wildcard_match(99) == "matched"
```

</details>

#### serves as catch-all

1. expect catchall match


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect catchall_match(42) == "other"
```

</details>

#### matches specific values first

1. expect catchall match
2. expect catchall match


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect catchall_match(0) == "zero"
expect catchall_match(1) == "one"
```

</details>

### enum patterns

#### unit enum variants

#### matches Red

1. expect match color


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_color(Color.Red) == "red"
```

</details>

#### matches Green

1. expect match color


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_color(Color.Green) == "green"
```

</details>

#### matches Blue

1. expect match color


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_color(Color.Blue) == "blue"
```

</details>

#### enum variants with payload

#### matches Some and extracts value

1. expect match option


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_option(MyOption.Some(42)) == 42
```

</details>

#### matches None

1. expect match option none default


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_option_none_default(MyOption.None) == 99
```

</details>

#### matches Ok result

1. expect match result ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_result_ok(MyResult.Ok(100)) == 100
```

</details>

#### matches Err result

1. expect match result err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_result_err(MyResult.Err("failed")) == "failed"
```

</details>

#### complex enum payloads

#### matches Circle and extracts radius

1. expect match shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_shape(Shape.Circle(5.0)) == 5.0
```

</details>

#### matches Rectangle and extracts first dimension

1. expect match shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multi-value enum variant: second binding not supported in interpreter.
# Returns width (first value) only.
expect match_shape(Shape.Rectangle(4.0, 3.0)) == 4.0
```

</details>

#### matches Point unit variant

1. expect match shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_shape(Shape.Point) == 0.0
```

</details>

### tuple patterns

#### basic tuple destructuring

#### destructures pair

1. expect match pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_pair((1, 2)) == 3
```

</details>

#### destructures triple

1. expect match triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_triple((1, 2, 3)) == 6
```

</details>

#### matches with partial wildcards

1. expect match pair first


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_pair_first((10, 20)) == 10
```

</details>

#### matches with all wildcards

1. expect match pair wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_pair_wildcard((1, 2)) == "matched"
```

</details>

#### nested tuple patterns

#### destructures nested tuples

1. expect match nested tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_nested_tuple(((1, 2), 3)) == 6
```

</details>

#### mixed tuple and literals

#### matches tuple with literal first element

1. expect match tuple literal first


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_literal_first((0, 42)) == 42
```

</details>

#### matches tuple with literal second element

1. expect match tuple literal second


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_literal_second((10, 0)) == 10
```

</details>

### struct field access

#### basic struct field access

#### accesses Point2D fields

1. expect match point


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D { x: 3, y: 4 }
expect match_point(p) == 7
```

</details>

#### accesses Person fields

1. expect match person age


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = Person { name: "Alice", age: 30 }
expect match_person_age(person) == 30
```

</details>

#### struct field comparison

#### matches origin point

1. expect match point origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D { x: 0, y: 0 }
expect match_point_origin(p) == "origin"
```

</details>

#### matches non-origin point

1. expect match point origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D { x: 5, y: 5 }
expect match_point_origin(p) == "not origin"
```

</details>

#### matches point on x-axis

1. expect match point axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D { x: 5, y: 0 }
expect match_point_axis(p) == "on x-axis"
```

</details>

#### matches point on y-axis

1. expect match point axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D { x: 0, y: 5 }
expect match_point_axis(p) == "on y-axis"
```

</details>

#### matches point elsewhere

1. expect match point axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D { x: 3, y: 4 }
expect match_point_axis(p) == "elsewhere"
```

</details>

### guard clauses

#### simple guards

#### matches with true guard

1. expect match with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_with_guard(10) == "big"
```

</details>

#### skips when guard is false

1. expect match with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_with_guard(3) == "small"
```

</details>

#### multiple guards

#### categorizes zero

1. expect categorize number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect categorize_number(0) == "zero"
```

</details>

#### categorizes small numbers

1. expect categorize number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect categorize_number(5) == "small"
```

</details>

#### categorizes medium numbers

1. expect categorize number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect categorize_number(50) == "medium"
```

</details>

#### categorizes large numbers

1. expect categorize number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect categorize_number(150) == "large"
```

</details>

#### guards with enums

#### uses guard on enum payload - large

1. expect match option with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_option_with_guard(MyOption.Some(150)) == "large"
```

</details>

#### uses guard on enum payload - medium

1. expect match option with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_option_with_guard(MyOption.Some(50)) == "medium"
```

</details>

#### uses guard on enum payload - small

1. expect match option with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_option_with_guard(MyOption.Some(5)) == "small"
```

</details>

#### handles None

1. expect match option with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_option_with_guard(MyOption.None) == "none"
```

</details>

#### guards with tuples

#### uses guard on tuple elements - sum is 7

1. expect match tuple with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_with_guard((3, 4)) == "sum is 7"
```

</details>

#### uses guard on tuple elements - equal

1. expect match tuple with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_with_guard((5, 5)) == "equal"
```

</details>

#### uses guard on tuple elements - other

1. expect match tuple with guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_with_guard((1, 2)) == "other"
```

</details>

### or patterns

#### literal alternatives

#### matches first alternative

1. expect match or pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_or_pattern(1) == "small"
```

</details>

#### matches middle alternative

1. expect match or pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_or_pattern(2) == "small"
```

</details>

#### matches last alternative

1. expect match or pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_or_pattern(3) == "small"
```

</details>

#### falls through when no match

1. expect match or pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_or_pattern(5) == "other"
```

</details>

#### enum alternatives

#### matches Red in or pattern

1. expect match color or


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_color_or(Color.Red) == "primary"
```

</details>

#### matches Blue in or pattern

1. expect match color or


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_color_or(Color.Blue) == "primary"
```

</details>

#### matches Green separately

1. expect match color or


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_color_or(Color.Green) == "secondary"
```

</details>

### range patterns

#### inclusive ranges

#### matches within range

1. expect match range


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_range(5) == "in range"
```

</details>

#### matches at lower bound

1. expect match range


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_range(1) == "in range"
```

</details>

#### matches at upper bound

1. expect match range


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_range(10) == "in range"
```

</details>

#### does not match outside range

1. expect match range


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_range(11) == "out of range"
```

</details>

#### categorizing with ranges

#### grades A

1. expect grade score


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect grade_score(95) == "A"
```

</details>

#### grades B

1. expect grade score


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect grade_score(85) == "B"
```

</details>

#### grades C

1. expect grade score


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect grade_score(75) == "C"
```

</details>

#### grades D

1. expect grade score


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect grade_score(65) == "D"
```

</details>

#### grades F

1. expect grade score


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect grade_score(55) == "F"
```

</details>

### array patterns

#### fixed-length arrays

#### matches single element

1. expect match single array


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_single_array([42]) == 42
```

</details>

#### matches two elements

1. expect match pair array


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_pair_array([1, 2]) == 3
```

</details>

#### returns default for wrong length

1. expect match single array


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_single_array([1, 2]) == 0
```

</details>

### if-val pattern

#### basic if-val

#### executes when pattern matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(42)
var result = 0
if val MyOption.Some(v) = opt:
    result = v
expect result == 42
```

</details>

#### skips when pattern does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.None
var result = 0
if val MyOption.Some(v) = opt:
    result = v
expect result == 0
```

</details>

#### if-val with else

#### executes else when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.None
var result = 0
if val MyOption.Some(v) = opt:
    result = v
else:
    result = 99
expect result == 99
```

</details>

#### executes then when matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(100)
var result = 0
if val MyOption.Some(v) = opt:
    result = v
else:
    result = 99
expect result == 100
```

</details>

#### if-val with tuples

#### destructures tuple in if-val

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (10, 20)
var result = 0
if val (a, b) = pair:
    result = a + b
expect result == 30
```

</details>

### complex pattern combinations

#### nested patterns

#### matches nested enum in tuple

1. expect match nested enum tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_nested_enum_tuple((MyOption.Some(42), "label")) == 42
```

</details>

#### matches None in tuple

1. expect match nested enum tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_nested_enum_tuple((MyOption.None, "label")) == 0
```

</details>

#### guards with complex patterns

#### uses guard on tuple values - large

1. expect match tuple guard complex


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_guard_complex((10, 20)) == "large sum"
```

</details>

#### uses guard on tuple values - small

1. expect match tuple guard complex


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect match_tuple_guard_complex((1, 2)) == "small sum"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/pattern_matching_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pattern Matching
- literal patterns
- variable binding patterns
- wildcard pattern
- enum patterns
- tuple patterns
- struct field access
- guard clauses
- or patterns
- range patterns
- array patterns
- if-val pattern
- complex pattern combinations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 79 |
| Active scenarios | 79 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
