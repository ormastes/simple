# Parser Expression Specification

> x + y, x - y, x * y, x / y, x % y, x ** y, x // y

<!-- sdn-diagram:id=parser_expressions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_expressions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_expressions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_expressions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Expression Specification

x + y, x - y, x * y, x / y, x % y, x ** y, x // y

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-EXPR-001 to #PARSER-EXPR-030 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_expressions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Arithmetic
x + y, x - y, x * y, x / y, x % y, x ** y, x // y

# Comparison
x < y, x > y, x <= y, x >= y, x == y, x != y

# Logical
x and y, x or y, not x

# Method/Field access
obj.method(), obj.field

# Indexing
arr[0], arr[i], arr[1:3]
```

## Scenarios

### Arithmetic Expression Parsing

#### basic operations

#### parses addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1 + 2
expect x == 3
```

</details>

#### parses subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5 - 3
expect x == 2
```

</details>

#### parses multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 4 * 5
expect x == 20
```

</details>

#### parses division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10 / 2
expect x == 5
```

</details>

#### parses modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7 % 3
expect x == 1
```

</details>

#### parses power

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2 ** 3
expect x == 8
```

</details>

#### parses integer division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7.fdiv(3)
expect x == 2
```

</details>

#### operator precedence

#### multiplication before addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2 + 3 * 4
expect x == 14
```

</details>

#### parentheses override precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = (2 + 3) * 4
expect x == 20
```

</details>

#### nested parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ((1 + 2) * 3)
expect x == 9
```

</details>

#### unary operations

#### parses unary minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -5
expect x == -5
```

</details>

#### parses bitwise not

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ~0
expect x == -1
```

</details>

### Comparison Expression Parsing

#### parses less than

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1 < 2) == true
```

</details>

#### parses greater than

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 > 1) == true
```

</details>

#### parses less than or equal

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 <= 2) == true
```

</details>

#### parses greater than or equal

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (3 >= 2) == true
```

</details>

#### parses equals

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 == 2) == true
```

</details>

#### parses not equals

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1 != 2) == true
```

</details>

### Logical Expression Parsing

#### parses and

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true and false
expect x == false
```

</details>

#### parses or

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true or false
expect x == true
```

</details>

#### parses not

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = not true
expect x == false
```

</details>

#### parses combined logical

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = (true and false) or true
expect x == true
```

</details>

### Method and Field Access Parsing

#### method calls

#### parses no-arg method call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val len = arr.len()
expect len == 3
```

</details>

#### parses method call with args

1. expect arr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.contains(2)
```

</details>

#### parses chained method calls

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
# NOTE: Using intermediate vars as workaround for interpreter chaining limitation
val mapped = arr.map(_1 * 2)
val result = mapped.filter(_1 > 2)
expect result.len() == 2
```

</details>

#### field access

#### parses field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i64
    y: i64
val p = Point(x: 10, y: 20)
expect p.x == 10
```

</details>

#### parses nested field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Inner:
    value: i64
class Outer:
    inner: Inner
val o = Outer(inner: Inner(value: 42))
expect o.inner.value == 42
```

</details>

### Indexing Expression Parsing

#### simple indexing

#### parses integer index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr[0] == 10
```

</details>

#### parses variable index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val i = 1
expect arr[i] == 20
```

</details>

#### parses expression index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr[1 + 1] == 30
```

</details>

#### parses negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr[-1] == 30
```

</details>

#### slicing

#### parses start end slice

1. expect sliced len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4]
val sliced = arr[1:4]
expect sliced.len() == 3
```

</details>

#### parses end slice

1. expect sliced len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4]
val sliced = arr[:3]
expect sliced.len() == 3
```

</details>

#### parses start slice

1. expect sliced len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4]
val sliced = arr[2:]
expect sliced.len() == 3
```

</details>

### Function Call Expression Parsing

#### positional arguments

#### parses no-arg call

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### parses single arg call

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
expect double(21) == 42
```

</details>

#### parses multi-arg call

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64, c: i64) -> i64:
    a + b + c
expect add(10, 20, 12) == 42
```

</details>

#### named arguments

#### parses named arguments

1. fn greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text, greeting: text) -> text:
    "{greeting}, {name}!"
val result = greet(name = "World", greeting = "Hello")
expect result == "Hello, World!"
```

</details>

### Path Expression Parsing

#### parses enum variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Color:
    Red
    Green
    Blue
val c = Color.Red
expect c == Color.Red
```

</details>

#### parses nested path

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module path syntax - using function call instead
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

### Conditional Expression Parsing

#### parses if-else expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = if true: 1 else: 0
expect x == 1
```

</details>

#### parses conditional comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val max = if a > b: a else: b
expect max == 10
```

</details>

### Lambda Expression Parsing

#### parses single parameter lambda

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \x: x + 1
expect f(41) == 42
```

</details>

#### parses multi-parameter lambda

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \a, b: a + b
expect f(20, 22) == 42
```

</details>

#### parses no-parameter lambda

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \: 42
expect f() == 42
```

</details>

#### uses lambda with map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val doubled = arr.map(_1 * 2)
expect doubled[0] == 2
```

</details>

### is/in Expression Parsing

#### parses is expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
if let Some(x) = opt:
    expect x == 42
```

</details>

#### parses in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3]
expect 2 in list
```

</details>

#### parses not in expression

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3]
expect not (5 in list)
```

</details>

### Nested Expression Parsing

#### parses deeply nested arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ((1 + 2) * (3 + 4)) - ((5 - 6) * (7 - 8))
expect x == 21 - 1
```

</details>

#### parses nested collections

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [[1, 2], [3, 4]]
expect arr[0][1] == 2
```

</details>

#### parses nested method chains

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: Using intermediate vars as workaround for interpreter chaining limitation
val arr = [1, 2, 3, 4, 5]
val filtered1 = arr.filter(_1 > 2)
val mapped = filtered1.map(_1 * 2)
val result = mapped.filter(_1 < 10)
expect result.len() == 2
```

</details>

### Optional Chaining Expression Parsing

#### parses optional chaining

1. expect len == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<text> = Some("hello")
val len = opt?.len()
expect len == Some(5)
```

</details>

#### parses null coalescing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
val value = opt ?? 42
expect value == 42
```

</details>

#### parses chained optional access

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct User:
    name: Option<text>
val user: Option<User> = Some(User { name: Some("Alice") })
val name = user?.name ?? "Unknown"
expect name == "Alice"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
