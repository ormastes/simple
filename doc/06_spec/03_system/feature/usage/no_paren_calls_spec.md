# No-Parentheses Function Calls Specification

> No-parentheses function calls allow calling functions without wrapping arguments in parentheses, providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

<!-- sdn-diagram:id=no_paren_calls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=no_paren_calls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

no_paren_calls_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=no_paren_calls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# No-Parentheses Function Calls Specification

No-parentheses function calls allow calling functions without wrapping arguments in parentheses, providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #300-310 |
| Category | Syntax |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/no_paren_calls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

No-parentheses function calls allow calling functions without wrapping arguments in parentheses,
providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function
calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

## Syntax

### Basic No-Paren Calls

```simple
print "Hello"              # print("Hello")
val result = add 2, 3      # val result = add(2, 3)
```

### With Field Access

```simple
obj.method arg             # obj.method(arg)
```

### With Trailing Lambdas

```simple
map numbers \x: x * 2      # map(numbers, \x: x * 2)
```

### With Colon-Blocks

```simple
describe "Feature":
test code
# describe("Feature", fn(): test code)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| No-Paren Call | Function call without wrapping arguments in `()` |
| Callable Expression | Identifier, field access, or path that can be called |
| Trailing Lambda | Lambda with `\` syntax as final argument |
| Colon-Block | Indented block after `:` becomes lambda argument |
| Comma Required | Arguments must be separated by commas in Normal mode |

## Behavior

- **Callable expressions**: Only identifiers, field access (`obj.method`), and paths (`Module.func`)
- **Comma-separated**: Multiple arguments require commas in Normal mode
- **Trailing lambda**: Backslash syntax (`\params: body`) can append lambda
- **Colon-block**: `:` followed by indent creates lambda argument
- **No nesting**: Strict mode disallows nested no-paren calls
- **Statement level**: Works at statement level, not within complex expressions

## Related Specifications

- [Trailing Blocks](../trailing_blocks/trailing_blocks_spec.md) - Lambda syntax with backslash
- [Functions](../functions/functions_spec.md) - Function definition and calling
- [Lambdas/Closures](../lambdas_closures/lambdas_closures_spec.md) - Lambda expressions

## Implementation Notes

**Parser:** `src/parser/src/expressions/no_paren.rs`
- `parse_with_no_paren_calls()` - Main entry point
- `is_callable_expr()` - Determines if expression can start no-paren call
- `can_start_argument()` - Checks if token can begin an argument

**Modes:**
- **Normal**: Default, allows nesting (may be ambiguous)
- **Strict**: GPU mode, disallows nested no-paren calls

**Performance:** No-paren calls desugar to regular calls during parsing - zero runtime overhead.

## Examples

```simple
# Basic calls
print "Hello World"
val sum = add 5, 10

# With field access
list.each item

# With trailing lambda
map items \x: x * 2
filter values \v: v > 0

# With colon-block
describe "Test":
it "works":
expect(result).to_equal(10)

# Multiple arguments
call arg1, arg2, arg3
```

## Scenarios

### No-Paren Calls - Basic Syntax

#### with single argument

#### calls function with single argument

1. fn double
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    x * 2

val result = double 5
expect(result).to_equal(10)
```

</details>

#### calls with literal argument

1. fn identity
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x

val result = identity 42
expect(result).to_equal(42)
```

</details>

#### calls with identifier argument

1. fn identity
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x

val value = 100
val result = identity value
expect(result).to_equal(100)
```

</details>

#### with multiple arguments

#### calls with two arguments

1. fn add
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    a + b

val result = add(10, 20)
expect(result).to_equal(30)
```

</details>

#### calls with three arguments

1. fn add3
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add3(a, b, c):
    a + b + c

val result = add3(5, 10, 15)
expect(result).to_equal(30)
```

</details>

#### mixes literals and identifiers

1. fn multiply
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(a, b):
    a * b

val factor = 5
val result = multiply(factor, 3)
expect(result).to_equal(15)
```

</details>

### No-Paren Calls - Argument Types

#### with literals

#### passes integer literal

1. fn identity
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x

val result = identity 42
expect(result).to_equal(42)
```

</details>

#### passes string literal

1. fn identity
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x

val result = identity "hello"
expect(result).to_equal("hello")
```

</details>

#### passes boolean literal

1. fn identity
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x

val result = identity true
expect(result).to_equal(true)
```

</details>

#### with parenthesized expressions

#### passes arithmetic expression

1. fn square
   - Expected: result equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x):
    x * x

val result = square (3 + 2)
expect(result).to_equal(25)
```

</details>

#### passes multiple expressions

1. fn add
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    a + b

val result = add((2 * 3), (4 + 5))
expect(result).to_equal(15)
```

</details>

### No-Paren Calls - Nested Calls

#### with inner parenthesized calls

#### nests parenthesized call

1. fn double
2. fn triple
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    x * 2

fn triple(x):
    x * 3

val result = double triple(5)
expect(result).to_equal(30)
```

</details>

#### chains multiple functions

1. fn add1
2. fn add2
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add1(x):
    x + 1

fn add2(x):
    x + 2

val result = add1 add2(10)
expect(result).to_equal(13)
```

</details>

### No-Paren Calls - Trailing Lambdas

#### with single argument plus lambda

#### accepts trailing lambda

1. fn apply
2. f
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(x, f):
    f(x)

val result = apply 5 \n: n * 2
expect(result).to_equal(10)
```

</details>

#### passes multiple args plus lambda

1. fn fold
2. acc = f
   - Expected: sum equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn fold(arr, init, f):
    var acc = init
    var i = 0
    while i < arr.len():
        acc = f(acc, arr[i])
        i = i + 1
    acc

val nums = [1, 2, 3]
val sum = fold(nums, 0) \acc, x: acc + x
expect(sum).to_equal(6)
```

</details>

### No-Paren Calls - Method Calls

#### with method calls

#### uses no-paren with helper function

1. fn get double func
2. fn inner
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_double_func():
    fn inner(x):
        x * 2
    inner

val double_func = get_double_func()
val result = double_func 21
expect(result).to_equal(42)
```

</details>

### No-Paren Calls - Context

#### in assignments

#### works in val assignments

1. fn double
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    x * 2

val result = double 10
expect(result).to_equal(20)
```

</details>

#### works in var assignments

1. fn add
2. var result = add
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    a + b

var result = add(5, 7)
expect(result).to_equal(12)
```

</details>

#### in return statements

#### works in implicit returns

1. fn wrapper
2. fn inner
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn wrapper(x):
    fn inner(n):
        n * 2
    inner x

val result = wrapper 7
expect(result).to_equal(14)
```

</details>

### No-Paren Calls - String Arguments

#### with string literals

#### passes single string

1. fn identity
   - Expected: result equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(s):
    s

val result = identity "test"
expect(result).to_equal("test")
```

</details>

#### passes string with spaces

1. fn identity
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(s):
    s

val result = identity "hello world"
expect(result).to_equal("hello world")
```

</details>

### No-Paren Calls - Mixed Syntax

#### with mixed styles

#### mixes paren and no-paren

1. fn add
2. fn double
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    a + b

fn double(x):
    x * 2

val result = add(double(5), 3)
expect(result).to_equal(13)
```

</details>

#### chains multiple mixed calls

1. fn add1
2. fn add2
3. fn add3
   - Expected: result equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add1(x):
    x + 1

fn add2(x):
    x + 2

fn add3(x):
    x + 3

val result = add1 add2(add3(10))
expect(result).to_equal(16)
```

</details>

### No-Paren Calls - Edge Cases

#### with zero arguments

#### requires parens for zero args

1. fn get value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value():
    42

val result = get_value()
expect(result).to_equal(42)
```

</details>

#### with single identifier

#### passes single variable

1. fn square
   - Expected: result equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x):
    x * x

val num = 7
val result = square num
expect(result).to_equal(49)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
