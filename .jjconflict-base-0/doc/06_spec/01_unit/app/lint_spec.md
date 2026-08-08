# Lint Specification

> 1. expect good name contains

<!-- sdn-diagram:id=lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Specification

## Scenarios

### Linter - code quality checks

#### validates variable naming conventions

1. expect good name contains

2. expect not bad name contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Variables should use snake_case
val good_name = "valid_variable"
val bad_name = "InvalidCamelCase"

# Test that snake_case is valid
expect good_name.contains("_")
expect not bad_name.contains("_")
```

</details>

#### validates function naming conventions

1. fn valid function name

2. fn InvalidFunctionName

3. expect valid function name

4. expect not InvalidFunctionName


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions should use snake_case
fn valid_function_name() -> bool:
    true

fn InvalidFunctionName() -> bool:
    false

expect valid_function_name()
expect not InvalidFunctionName()
```

</details>

#### validates class naming conventions

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Classes should use PascalCase
class ValidClassName:
    value: i64

class invalid_class_name:
    value: i64

val good_class = ValidClassName(value: 1)
val bad_class = invalid_class_name(value: 2)

expect good_class.value == 1
expect bad_class.value == 2
```

</details>

### Linter - code patterns

#### detects unused variable declarations

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would normally be flagged by linter
var unused_var = 42
var used_var = 10

# Using used_var
val result = used_var * 2
expect result == 20
```

</details>

#### detects missing return type annotations

1. fn no return type

2. fn with return type

3. expect no return type

4. expect with return type


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function without explicit return type
fn no_return_type(x):
    x * 2

# Function with explicit return type
fn with_return_type(x: i64) -> i64:
    x * 2

expect no_return_type(5) == 10
expect with_return_type(5) == 10
```

</details>

#### validates error handling patterns

1. fn may fail

2. Err

3. Ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions that can fail should return Result
fn may_fail(x: i64) -> Result<i64, text>:
    if x < 0:
        Err("Negative value")
    else:
        Ok(x * 2)

val result = may_fail(5)
match result:
    case Ok(value):
        expect value == 10
    case Err(msg):
        expect msg == ""
```

</details>

### Linter - best practices

#### prefers val over var when possible

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Immutable by default
val immutable = 42
var mutable = 10

# Can reassign mutable
mutable = mutable + 5
expect mutable == 15

# Cannot reassign immutable (would be caught by linter)
expect immutable == 42
```

</details>

#### validates proper use of Option types

1. fn find value


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions returning optional values
fn find_value(arr: [i64], target: i64) -> Option<i64>:
    for item in arr:
        if item == target:
            return Some(item)
    None

val result = find_value([1, 2, 3], 2)
match result:
    case Some(v):
        expect v == 2
    case None:
        expect("Expected target value to be found" == "")
```

</details>

#### validates match exhaustiveness

1. fn describe color


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All cases should be covered
enum Color:
    Red
    Green
    Blue

fn describe_color(c: Color) -> text:
    match c:
        case Color.Red:
            "red"
        case Color.Green:
            "green"
        case Color.Blue:
            "blue"

val desc = describe_color(Color.Red)
expect desc == "red"
```

</details>

### Linter - performance hints

<details>
<summary>Advanced: suggests using iterators over loops</summary>

#### suggests using iterators over loops

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Less efficient: manual loop
var sum1 = 0
for i in [1, 2, 3, 4, 5]:
    sum1 = sum1 + i

# More efficient: using iterator methods
val sum2 = [1, 2, 3, 4, 5].sum()

expect sum1 == 15
expect sum2 == 15
```

</details>


</details>

#### suggests const for compile-time constants

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Should be const, not val
val PI_VAL = 3.14159
const PI_CONST = 3.14159

expect PI_VAL > 3.0
expect PI_CONST > 3.0
```

</details>

### Linter - accessor and inherited name checks

#### warns for trivial get set is accessors

1. "    fn get value

2. "    fn set value

3. "    fn is active
   - Expected: count_name_lint(source, "ACC001") equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "class Meter:\n" +
    "    value: i64\n" +
    "    active: bool\n" +
    "    fn get_value(self) -> i64:\n" +
    "        self.value\n" +
    "    fn set_value(self, value: i64):\n" +
    "        self.value = value\n" +
    "    fn is_active(self) -> bool:\n" +
    "        self.active\n"
expect(count_name_lint(source, "ACC001")).to_equal(3)
```

</details>

#### suppresses a trivial accessor group when any accessor has real behavior

1. "    fn get value

2. "    fn set value
   - Expected: count_name_lint(source, "ACC001") equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "class Meter:\n" +
    "    value: i64\n" +
    "    fn get_value(self) -> i64:\n" +
    "        if self.value < 0:\n" +
    "            return 0\n" +
    "        self.value\n" +
    "    fn set_value(self, value: i64):\n" +
    "        self.value = value\n"
expect(count_name_lint(source, "ACC001")).to_equal(0)
```

</details>

#### suppresses dummy accessor warning when overriding a parent accessor

1. "    fn get value

2. "    fn get value
   - Expected: count_name_lint(source, "ACC001") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "class Parent:\n" +
    "    value: i64\n" +
    "    fn get_value(self) -> i64:\n" +
    "        self.value\n" +
    "class Child extends Parent:\n" +
    "    value: i64\n" +
    "    fn get_value(self) -> i64:\n" +
    "        self.value\n"
expect(count_name_lint(source, "ACC001")).to_equal(1)
```

</details>

#### warns for close misspellings of inherited method names

1. "    fn render frame

2. "    fn render farme
   - Expected: count_name_lint(source, "NAME001") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "class Parent:\n" +
    "    fn render_frame(self):\n" +
    "        pass\n" +
    "class Child extends Parent:\n" +
    "    fn render_farme(self):\n" +
    "        pass\n"
expect(count_name_lint(source, "NAME001")).to_equal(1)
```

</details>

#### suppresses close inherited method name warning with name_checked

1. "    fn render frame

2. "    fn render farme
   - Expected: count_name_lint(source, "NAME001") equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "class Parent:\n" +
    "    fn render_frame(self):\n" +
    "        pass\n" +
    "class Child extends Parent:\n" +
    "    @name_checked\n" +
    "    fn render_farme(self):\n" +
    "        pass\n"
expect(count_name_lint(source, "NAME001")).to_equal(0)
```

</details>

#### treats name_checked as a known Pure Simple annotation

1. "    fn render farme
   - Expected: check_unknown_decorator(source, "sample.spl").len() equals `0`
   - Expected: check_unknown_attribute(source, "sample.spl").len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "class Child:\n" +
    "    @name_checked\n" +
    "    fn render_farme(self):\n" +
    "        pass\n"
expect(check_unknown_decorator(source, "sample.spl").len()).to_equal(0)
expect(check_unknown_attribute(source, "sample.spl").len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linter - code quality checks
- Linter - code patterns
- Linter - best practices
- Linter - performance hints
- Linter - accessor and inherited name checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
