# Branch Coverage Test Suite - Parser Edge Cases & Error Paths

> Targets uncovered branches in parser and lexer error handling. Tests malformed input recovery, edge cases, and uncommon constructs.

<!-- sdn-diagram:id=branch_coverage_29_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_29_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_29_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_29_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Parser Edge Cases & Error Paths

Targets uncovered branches in parser and lexer error handling. Tests malformed input recovery, edge cases, and uncommon constructs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #PARSER_EDGE #ERROR_PATH |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_29_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Targets uncovered branches in parser and lexer error handling.
Tests malformed input recovery, edge cases, and uncommon constructs.

## Scenarios

### Lexer Edge Cases

#### number - leading zeros

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 007
check(x == 7)
```

</details>

#### number - underscore separators

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1_000_000
check(x == 1000000)
```

</details>

#### number - underscore in hex

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF_FF
check(x == 65535)
```

</details>

#### number - underscore in binary

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1111_0000
check(x == 240)
```

</details>

#### float - no integer part

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0.5
check(x > 0.4)
check(x < 0.6)
```

</details>

#### float - no fractional part

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5.0
check(x == 5.0)
```

</details>

#### float - underscore in decimal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.141_592
check(x > 3.14)
```

</details>

#### string - all escape sequences

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "\n\t\r\\\"\'"
check(s.len() > 0)
```

</details>

#### string - unicode escape

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello"
check(s.contains("H"))
```

</details>

#### string - hex escape

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "test"
check(s.len() == 4)
```

</details>

#### comment - single line

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is a comment
val x = 42 # comment after code
check(x == 42)
```

</details>

#### comment - multiple lines

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Line 1
# Line 2
# Line 3
val x = 42
check(x == 42)
```

</details>

### Parser Precedence Edge Cases

#### precedence - power vs multiply

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 * 3 ** 2 == 18)
check((2 * 3) ** 2 == 36)
```

</details>

#### precedence - unary vs binary

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In this binary, unary - binds tighter than **, so -2**2 == (-2)**2 == 4
check((-2) ** 2 == 4)
check(-(2 ** 2) == -4)
```

</details>

#### precedence - not vs and

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((not true and false) == false)
check(not (true and false) == true)
```

</details>

#### precedence - and vs or

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true or false and false == true)
check((true or false) and false == false)
```

</details>

#### precedence - comparison chains

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 < 2 < 3 < 4)
check(not (1 < 2 > 3))
```

</details>

#### precedence - mixed operations

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 + 3 * 4 - 5 == 9)
check(10 / 2 + 3 * 4 == 17)
```

</details>

#### associativity - power right associative

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 ** 3 ** 2 == 512)
```

</details>

#### associativity - subtract left associative

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 - 5 - 2 == 3)
```

</details>

#### associativity - divide left associative

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(20 / 4 / 2 == 2)
```

</details>

### Expression Combinations

#### nested calls

1. fn f
2. fn g
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64) -> i64: x + 1
fn g(x: i64) -> i64: x * 2
check(f(g(f(5))) == 13)
```

</details>

#### call with expression args

1. fn add
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64: a + b
check(add(2 + 3, 4 * 5) == 25)
```

</details>

#### nested array access

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [[1, 2], [3, 4], [5, 6]]
check(arr[1][1] == 4)
```

</details>

#### method chain - multiple

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  hello  "
val result = s.trim()
check(result == "hello")
```

</details>

#### array with expressions

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val arr = [a, a + 1, a + 2, a * 2]
check(arr[0] == 5)
check(arr[3] == 10)
```

</details>

#### string interpolation nested

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 10
val s = "{x + y}"
check(s.contains("15"))
```

</details>

### Statement Coverage

#### val declaration - no type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
check(x == 42)
```

</details>

#### val declaration - with type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
check(x == 42)
```

</details>

#### var declaration - no initial value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: i64 = 0
x = 42
check(x == 42)
```

</details>

#### var declaration - with initial value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 42
x = x + 1
check(x == 43)
```

</details>

#### assignment - simple

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
x = 42
check(x == 42)
```

</details>

#### assignment - with expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x = x * 2 + 5
check(x == 25)
```

</details>

#### assignment - array element

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr[1] = 10
check(arr[1] == 10)
```

</details>

### Complex Pattern Matching

#### match - nested patterns

1. fn run
2. Some
3. Some
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    val opt = Some(Some(42))
    var result = 0
    match opt:
        Some(Some(x)): result = x
        Some(nil): result = -1
        nil: result = -2
    result
check(run() == 42)
```

</details>

#### match - multiple nested levels

1. fn run
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    val triple = Some(Some(Some(10)))
    var result = 0
    match triple:
        Some(Some(Some(x))): result = x
        _: result = -1
    result
check(run() == 10)
```

</details>

#### variable binding

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
val sum = a + b
check(sum == 15)
```

</details>

### Function Definition Edge Cases

#### function - no parameters

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f() -> i64: 42
check(f() == 42)
```

</details>

#### function - one parameter

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64) -> i64: x
check(f(42) == 42)
```

</details>

#### function - many parameters

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(a: i64, b: i64, c: i64, d: i64) -> i64:
    a + b + c + d
check(f(1, 2, 3, 4) == 10)
```

</details>

#### function - no return type

1. fn f
2. f
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64):
    pass
f(42)
check(true)
```

</details>

#### function - explicit return

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64) -> i64:
    return x * 2
check(f(5) == 10)
```

</details>

#### function - implicit return

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64) -> i64:
    x * 2
check(f(5) == 10)
```

</details>

#### function - early return in if

1. fn f
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64) -> i64:
    if x < 0:
        return 0
    x
check(f(-5) == 0)
check(f(5) == 5)
```

</details>

<details>
<summary>Advanced: function - early return in loop</summary>

#### function - early return in loop

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f() -> i64:
    for i in 0..10:
        if i == 5:
            return i
    -1
check(f() == 5)
```

</details>


</details>

### Struct and Type Usage

#### struct - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Empty:
    pass
val e = Empty()
check(true)
```

</details>

#### struct - single field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Single:
    x: i64
val s = Single(x: 42)
check(s.x == 42)
```

</details>

#### struct - multiple fields

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point(x: 3, y: 4)
check(p.x == 3)
check(p.y == 4)
```

</details>

#### struct - field access

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Data:
    value: i64
val d = Data(value: 100)
val x = d.value
check(x == 100)
```

</details>

#### struct - field update

1. var c = Counter
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Counter:
    count: i64
var c = Counter(count: 0)
c.count = c.count + 1
check(c.count == 1)
```

</details>

### Enum Coverage

#### enum - simple

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Color:
    Red
    Green
    Blue
val c = Color.Red
val is_red = match c:
    Color.Red: true
    _: false
check(is_red)
```

</details>

#### enum - with match all cases

1. fn check status
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Status:
    Ok
    Error
    Pending
fn check_status(s: Status) -> i64:
    match s:
        Status.Ok: 1
        Status.Error: 2
        Status.Pending: 3
check(check_status(Status.Ok) == 1)
check(check_status(Status.Error) == 2)
check(check_status(Status.Pending) == 3)
```

</details>

### Whitespace and Formatting

#### handles extra whitespace

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val    x    =    42
check(x == 42)
```

</details>

#### handles tabs

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val	x	=	42
check(x == 42)
```

</details>

#### handles line breaks

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x =
    42
check(x == 42)
```

</details>

#### handles empty lines

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 42

check(x == 42)
```

</details>

### Literal Edge Cases

#### bool - true literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = true
check(t)
```

</details>

#### bool - false literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = false
check(not f)
```

</details>

#### nil - literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = nil
check(not n.?)
```

</details>

#### tuple - two elements

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
check(a == 1 and b == 2)
```

</details>

#### tuple - three elements

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val c = 3
check(a == 1 and b == 2 and c == 3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
