# Pattern Matching Specification

> Tests covering Pattern Matching, literal patterns, variable binding patterns, wildcard pattern, enum patterns, tuple patterns, struct field access, guard clauses, or patterns, range patterns, array patterns, if-val pattern, complex pattern combinations.

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

- matches zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches zero")
expect match_int(0) == "zero"
```

</details>

#### matches positive integers

- matches positive integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches positive integers")
expect match_int(42) == "found"
```

</details>

#### matches larger integers

- matches larger integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches larger integers")
expect match_int(100) == "hundred"
```

</details>

#### uses wildcard for unmatched

- uses wildcard for unmatched


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses wildcard for unmatched")
expect match_int(999) == "other"
```

</details>

#### boolean literals

#### matches true

- matches true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches true")
expect match_bool(true) == "yes"
```

</details>

#### matches false

- matches false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches false")
expect match_bool(false) == "no"
```

</details>

#### string literals

#### matches string values

- matches string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches string values")
expect match_string("hello") == "greeting"
```

</details>

#### matches empty string

- matches empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches empty string")
expect match_string("") == "empty"
```

</details>

#### uses wildcard for unmatched strings

- uses wildcard for unmatched strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses wildcard for unmatched strings")
expect match_string("other") == "unknown"
```

</details>

### variable binding patterns

#### simple binding

#### binds value to variable

- binds value to variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("binds value to variable")
expect double_via_match(42) == 84
```

</details>

#### binds and uses in expression

- binds and uses in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("binds and uses in expression")
expect add_five_via_match(10) == 15
```

</details>

### wildcard pattern

#### basic wildcards

#### matches anything

- matches anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches anything")
expect wildcard_match(99) == "matched"
```

</details>

#### serves as catch-all

- serves as catch-all


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("serves as catch-all")
expect catchall_match(42) == "other"
```

</details>

#### matches specific values first

- matches specific values first


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches specific values first")
expect catchall_match(0) == "zero"
expect catchall_match(1) == "one"
```

</details>

### enum patterns

#### unit enum variants

#### matches Red

- matches Red


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Red")
expect match_color(Color.Red) == "red"
```

</details>

#### matches Green

- matches Green


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Green")
expect match_color(Color.Green) == "green"
```

</details>

#### matches Blue

- matches Blue


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Blue")
expect match_color(Color.Blue) == "blue"
```

</details>

#### enum variants with payload

#### matches Some and extracts value

- matches Some and extracts value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Some and extracts value")
expect match_option(MyOption.Some(42)) == 42
```

</details>

#### matches None

- matches None


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches None")
expect match_option_none_default(MyOption.None) == 99
```

</details>

#### matches Ok result

- matches Ok result


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Ok result")
expect match_result_ok(MyResult.Ok(100)) == 100
```

</details>

#### matches Err result

- matches Err result


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Err result")
expect match_result_err(MyResult.Err("failed")) == "failed"
```

</details>

#### complex enum payloads

#### matches Circle and extracts radius

- matches Circle and extracts radius


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Circle and extracts radius")
expect match_shape(Shape.Circle(5.0)) == 5.0
```

</details>

#### matches Rectangle and extracts first dimension

- matches Rectangle and extracts first dimension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Rectangle and extracts first dimension")
# Multi-value enum variant: second binding not supported in interpreter.
# Returns width (first value) only.
expect match_shape(Shape.Rectangle(4.0, 3.0)) == 4.0
```

</details>

#### matches Point unit variant

- matches Point unit variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Point unit variant")
expect match_shape(Shape.Point) == 0.0
```

</details>

### tuple patterns

#### basic tuple destructuring

#### destructures pair

- destructures pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("destructures pair")
expect match_pair((1, 2)) == 3
```

</details>

#### destructures triple

- destructures triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("destructures triple")
expect match_triple((1, 2, 3)) == 6
```

</details>

#### matches with partial wildcards

- matches with partial wildcards


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches with partial wildcards")
expect match_pair_first((10, 20)) == 10
```

</details>

#### matches with all wildcards

- matches with all wildcards


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches with all wildcards")
expect match_pair_wildcard((1, 2)) == "matched"
```

</details>

#### nested tuple patterns

#### destructures nested tuples

- destructures nested tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("destructures nested tuples")
expect match_nested_tuple(((1, 2), 3)) == 6
```

</details>

#### mixed tuple and literals

#### matches tuple with literal first element

- matches tuple with literal first element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches tuple with literal first element")
expect match_tuple_literal_first((0, 42)) == 42
```

</details>

#### matches tuple with literal second element

- matches tuple with literal second element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches tuple with literal second element")
expect match_tuple_literal_second((10, 0)) == 10
```

</details>

### struct field access

#### basic struct field access

#### accesses Point2D fields

- accesses Point2D fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("accesses Point2D fields")
val p = Point2D { x: 3, y: 4 }
expect match_point(p) == 7
```

</details>

#### accesses Person fields

- accesses Person fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("accesses Person fields")
val person = Person { name: "Alice", age: 30 }
expect match_person_age(person) == 30
```

</details>

#### struct field comparison

#### matches origin point

- matches origin point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches origin point")
val p = Point2D { x: 0, y: 0 }
expect match_point_origin(p) == "origin"
```

</details>

#### matches non-origin point

- matches non-origin point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches non-origin point")
val p = Point2D { x: 5, y: 5 }
expect match_point_origin(p) == "not origin"
```

</details>

#### matches point on x-axis

- matches point on x-axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches point on x-axis")
val p = Point2D { x: 5, y: 0 }
expect match_point_axis(p) == "on x-axis"
```

</details>

#### matches point on y-axis

- matches point on y-axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches point on y-axis")
val p = Point2D { x: 0, y: 5 }
expect match_point_axis(p) == "on y-axis"
```

</details>

#### matches point elsewhere

- matches point elsewhere


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches point elsewhere")
val p = Point2D { x: 3, y: 4 }
expect match_point_axis(p) == "elsewhere"
```

</details>

### guard clauses

#### simple guards

#### matches with true guard

- matches with true guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches with true guard")
expect match_with_guard(10) == "big"
```

</details>

#### skips when guard is false

- skips when guard is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("skips when guard is false")
expect match_with_guard(3) == "small"
```

</details>

#### multiple guards

#### categorizes zero

- categorizes zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("categorizes zero")
expect categorize_number(0) == "zero"
```

</details>

#### categorizes small numbers

- categorizes small numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("categorizes small numbers")
expect categorize_number(5) == "small"
```

</details>

#### categorizes medium numbers

- categorizes medium numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("categorizes medium numbers")
expect categorize_number(50) == "medium"
```

</details>

#### categorizes large numbers

- categorizes large numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("categorizes large numbers")
expect categorize_number(150) == "large"
```

</details>

#### guards with enums

#### uses guard on enum payload - large

- uses guard on enum payload - large


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on enum payload - large")
expect match_option_with_guard(MyOption.Some(150)) == "large"
```

</details>

#### uses guard on enum payload - medium

- uses guard on enum payload - medium


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on enum payload - medium")
expect match_option_with_guard(MyOption.Some(50)) == "medium"
```

</details>

#### uses guard on enum payload - small

- uses guard on enum payload - small


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on enum payload - small")
expect match_option_with_guard(MyOption.Some(5)) == "small"
```

</details>

#### handles None

- handles None


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("handles None")
expect match_option_with_guard(MyOption.None) == "none"
```

</details>

#### guards with tuples

#### uses guard on tuple elements - sum is 7

- uses guard on tuple elements - sum is 7


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on tuple elements - sum is 7")
expect match_tuple_with_guard((3, 4)) == "sum is 7"
```

</details>

#### uses guard on tuple elements - equal

- uses guard on tuple elements - equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on tuple elements - equal")
expect match_tuple_with_guard((5, 5)) == "equal"
```

</details>

#### uses guard on tuple elements - other

- uses guard on tuple elements - other


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on tuple elements - other")
expect match_tuple_with_guard((1, 2)) == "other"
```

</details>

### or patterns

#### literal alternatives

#### matches first alternative

- matches first alternative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches first alternative")
expect match_or_pattern(1) == "small"
```

</details>

#### matches middle alternative

- matches middle alternative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches middle alternative")
expect match_or_pattern(2) == "small"
```

</details>

#### matches last alternative

- matches last alternative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches last alternative")
expect match_or_pattern(3) == "small"
```

</details>

#### falls through when no match

- falls through when no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("falls through when no match")
expect match_or_pattern(5) == "other"
```

</details>

#### enum alternatives

#### matches Red in or pattern

- matches Red in or pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Red in or pattern")
expect match_color_or(Color.Red) == "primary"
```

</details>

#### matches Blue in or pattern

- matches Blue in or pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Blue in or pattern")
expect match_color_or(Color.Blue) == "primary"
```

</details>

#### matches Green separately

- matches Green separately


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches Green separately")
expect match_color_or(Color.Green) == "secondary"
```

</details>

### range patterns

#### inclusive ranges

#### matches within range

- matches within range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches within range")
expect match_range(5) == "in range"
```

</details>

#### matches at lower bound

- matches at lower bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches at lower bound")
expect match_range(1) == "in range"
```

</details>

#### matches at upper bound

- matches at upper bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches at upper bound")
expect match_range(10) == "in range"
```

</details>

#### does not match outside range

- does not match outside range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("does not match outside range")
expect match_range(11) == "out of range"
```

</details>

#### categorizing with ranges

#### grades A

- grades A


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("grades A")
expect grade_score(95) == "A"
```

</details>

#### grades B

- grades B


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("grades B")
expect grade_score(85) == "B"
```

</details>

#### grades C

- grades C


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("grades C")
expect grade_score(75) == "C"
```

</details>

#### grades D

- grades D


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("grades D")
expect grade_score(65) == "D"
```

</details>

#### grades F

- grades F


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("grades F")
expect grade_score(55) == "F"
```

</details>

### array patterns

#### fixed-length arrays

#### matches single element

- matches single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches single element")
expect match_single_array([42]) == 42
```

</details>

#### matches two elements

- matches two elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches two elements")
expect match_pair_array([1, 2]) == 3
```

</details>

#### returns default for wrong length

- returns default for wrong length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns default for wrong length")
expect match_single_array([1, 2]) == 0
```

</details>

### if-val pattern

#### basic if-val

#### executes when pattern matches

- executes when pattern matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("executes when pattern matches")
val opt = MyOption.Some(42)
var result = 0
if val MyOption.Some(v) = opt:
    result = v
expect result == 42
```

</details>

#### skips when pattern does not match

- skips when pattern does not match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("skips when pattern does not match")
val opt = MyOption.None
var result = 0
if val MyOption.Some(v) = opt:
    result = v
expect result == 0
```

</details>

#### if-val with else

#### executes else when no match

- executes else when no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("executes else when no match")
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

- executes then when matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("executes then when matches")
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

- destructures tuple in if-val


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("destructures tuple in if-val")
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

- matches nested enum in tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches nested enum in tuple")
expect match_nested_enum_tuple((MyOption.Some(42), "label")) == 42
```

</details>

#### matches None in tuple

- matches None in tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches None in tuple")
expect match_nested_enum_tuple((MyOption.None, "label")) == 0
```

</details>

#### guards with complex patterns

#### uses guard on tuple values - large

- uses guard on tuple values - large


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on tuple values - large")
expect match_tuple_guard_complex((10, 20)) == "large sum"
```

</details>

#### uses guard on tuple values - small

- uses guard on tuple values - small


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses guard on tuple values - small")
expect match_tuple_guard_complex((1, 2)) == "small sum"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/pattern_matching_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Pattern Matching, literal patterns, variable binding patterns, wildcard pattern, enum patterns, tuple patterns, struct field access, guard clauses, or patterns, range patterns, array patterns, if-val pattern, complex pattern combinations.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `455aeed76e704224cfaddccf5a4a09860ba7c8386982ef702e10bf365a67c19c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `455aeed76e704224cfaddccf5a4a09860ba7c8386982ef702e10bf365a67c19c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `455aeed76e704224cfaddccf5a4a09860ba7c8386982ef702e10bf365a67c19c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/types/pattern_matching_spec.spl
mirror: doc/06_spec/shared/types/pattern_matching_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/types/pattern_matching_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/types/pattern_matching_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/types/pattern_matching_spec.spl:331:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/pattern_matching_spec.spl:336:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches positive integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/pattern_matching_spec.spl:341:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches larger integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
