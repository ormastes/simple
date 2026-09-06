# Default Parameter Values

> Tests the `default` keyword for function parameter default values using `=` syntax. Covers basic defaults, typed parameters, methods (instance and static), collection defaults, edge cases (booleans, negatives, expressions), and combinations of required and default parameters across functions, classes, and nested scopes.

<!-- sdn-diagram:id=parser_default_keyword_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_default_keyword_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_default_keyword_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_default_keyword_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default Parameter Values

Tests the `default` keyword for function parameter default values using `=` syntax. Covers basic defaults, typed parameters, methods (instance and static), collection defaults, edge cases (booleans, negatives, expressions), and combinations of required and default parameters across functions, classes, and nested scopes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-001 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/parser_default_keyword_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `default` keyword for function parameter default values using `=`
syntax. Covers basic defaults, typed parameters, methods (instance and static),
collection defaults, edge cases (booleans, negatives, expressions), and
combinations of required and default parameters across functions, classes,
and nested scopes.

## Syntax

```simple
fn greet(name = "World"):
return "Hello, {name}"
fn typed_default(count: i32 = 0):
return count
```

## Scenarios

### Default keyword in function parameters

#### parses default parameter value with = syntax

1. fn greet
2. expect greet
3. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name = "World"):
    return "Hello, {name}"
expect greet() == "Hello, World"
expect greet("Alice") == "Hello, Alice"
```

</details>

#### parses multiple default parameters

1. fn create range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_range(min = 0, max = 100):
    return [min, max]
val range = create_range()
expect range[0] == 0
expect range[1] == 100
```

</details>

#### overrides single default parameter

1. fn with defaults
2. expect with defaults
3. expect with defaults
4. expect with defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_defaults(x = 1, y = 2):
    return x + y
expect with_defaults() == 3
expect with_defaults(5) == 7
expect with_defaults(5, 10) == 15
```

</details>

#### parses default with expressions

1. fn with expr default
2. expect with expr default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_expr_default(size = 2 ** 10):
    return size
expect with_expr_default() == 1024
```

</details>

#### parses default with arithmetic

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute(base = 100, offset = 10 + 5):
    return base + offset
expect compute() == 115
```

</details>

#### uses default in nested function

1. fn outer
2. fn inner
3. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer():
    fn inner(value = 42):
        return value
    return inner()
expect outer() == 42
```

</details>

### Default keyword with types

#### parses default parameter with type annotation

1. fn typed default
2. expect typed default
3. expect typed default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn typed_default(count: i32 = 0):
    return count
expect typed_default() == 0
expect typed_default(5) == 5
```

</details>

#### parses default text parameter

1. fn with text
2. expect with text
3. expect with text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_text(message: text = "default"):
    return message
expect with_text() == "default"
expect with_text("custom") == "custom"
```

</details>

#### parses default float parameter

1. fn with float
2. expect with float


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_float(value: f64 = 3.14):
    return value
expect with_float() > 3.0
```

</details>

### Default keyword in methods

#### parses default in class method

1. me increment
2. var c = Counter
3. c increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i32

    me increment(amount = 1):
        self.value = self.value + amount

var c = Counter(value: 10)
c.increment()
expect c.value == 11
```

</details>

#### parses default in static method

1. static fn create
2. expect Factory create
3. expect Factory create


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Factory:
    static fn create(size = 10) -> i32:
        return size

expect Factory.create() == 10
expect Factory.create(20) == 20
```

</details>

### Default keyword with collections

#### parses default empty array

1. fn with array
2. expect with array
3. expect with array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_array(items = []):
    return items.len()
expect with_array() == 0
expect with_array([1, 2, 3]) == 3
```

</details>

#### parses default array literal

1. fn with values
2. expect with values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_values(data = [1, 2, 3]):
    return data.len()
expect with_values() == 3
```

</details>

### Default keyword edge cases

#### parses default with boolean

1. fn with flag
2. expect with flag
3. expect with flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_flag(enabled = true):
    return enabled
expect with_flag() == true
expect with_flag(false) == false
```

</details>

#### parses default with negative number

1. fn with negative
2. expect with negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn with_negative(value = -10):
    return value
expect with_negative() == -10
```

</details>

#### parses default with string interpolation

1. fn greet default
2. expect greet default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_name = "World"
fn greet_default(name = default_name):
    return "Hello, {name}"
expect greet_default() == "Hello, World"
```

</details>

### Default keyword combinations

#### parses mix of required and default parameters

1. fn mixed
2. expect mixed
3. expect mixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn mixed(required, optional = 5):
    return required + optional
expect mixed(10) == 15
expect mixed(10, 20) == 30
```

</details>

#### parses multiple functions with defaults

1. fn first
2. fn second
3. expect first
4. expect second


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn first(x = 1):
    return x
fn second(y = 2):
    return y
expect first() == 1
expect second() == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
