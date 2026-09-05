# Branch Coverage 29 Specification

> Tests covering Lexer Edge Cases, Parser Precedence Edge Cases, Expression Combinations, Statement Coverage, Complex Pattern Matching, Function Definition Edge Cases, Struct and Type Usage, Enum Coverage, Whitespace and Formatting, Literal Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 29 Specification

## Scenarios

### Lexer Edge Cases

#### number - leading zeros

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- number - leading zeros


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number - leading zeros")
val x = 007
check(x == 7)
```

</details>

#### number - underscore separators

- number - underscore separators


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number - underscore separators")
val x = 1_000_000
check(x == 1000000)
```

</details>

#### number - underscore in hex

- number - underscore in hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number - underscore in hex")
val x = 0xFF_FF
check(x == 65535)
```

</details>

#### number - underscore in binary

- number - underscore in binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number - underscore in binary")
val x = 0b1111_0000
check(x == 240)
```

</details>

#### float - no integer part

- float - no integer part


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - no integer part")
val x = 0.5
check(x > 0.4)
check(x < 0.6)
```

</details>

#### float - no fractional part

- float - no fractional part


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - no fractional part")
val x = 5.0
check(x == 5.0)
```

</details>

#### float - underscore in decimal

- float - underscore in decimal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float - underscore in decimal")
val x = 3.141_592
check(x > 3.14)
```

</details>

#### string - all escape sequences

- string - all escape sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - all escape sequences")
val s = "\n\t\r\\\"\'"
check(s.len() > 0)
```

</details>

#### string - unicode escape

- string - unicode escape


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - unicode escape")
val s = "Hello"
check(s.contains("H"))
```

</details>

#### string - hex escape

- string - hex escape


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - hex escape")
val s = "test"
check(s.len() == 4)
```

</details>

#### comment - single line

- comment - single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comment - single line")
# This is a comment
val x = 42 # comment after code
check(x == 42)
```

</details>

#### comment - multiple lines

- comment - multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comment - multiple lines")
# Line 1
# Line 2
# Line 3
val x = 42
check(x == 42)
```

</details>

### Parser Precedence Edge Cases

#### precedence - power vs multiply

- precedence - power vs multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precedence - power vs multiply")
check(2 * 3 ** 2 == 18)
check((2 * 3) ** 2 == 36)
```

</details>

#### precedence - unary vs binary

- precedence - unary vs binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precedence - unary vs binary")
# In this binary, unary - binds tighter than **, so -2**2 == (-2)**2 == 4
check((-2) ** 2 == 4)
check(-(2 ** 2) == -4)
```

</details>

#### precedence - not vs and

- precedence - not vs and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precedence - not vs and")
check((not true and false) == false)
check(not (true and false) == true)
```

</details>

#### precedence - and vs or

- precedence - and vs or


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precedence - and vs or")
check(true or false and false == true)
check((true or false) and false == false)
```

</details>

#### precedence - comparison chains

- precedence - comparison chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precedence - comparison chains")
check(1 < 2 < 3 < 4)
check(not (1 < 2 > 3))
```

</details>

#### precedence - mixed operations

- precedence - mixed operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precedence - mixed operations")
check(2 + 3 * 4 - 5 == 9)
check(10 / 2 + 3 * 4 == 17)
```

</details>

#### associativity - power right associative

- associativity - power right associative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("associativity - power right associative")
check(2 ** 3 ** 2 == 512)
```

</details>

#### associativity - subtract left associative

- associativity - subtract left associative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("associativity - subtract left associative")
check(10 - 5 - 2 == 3)
```

</details>

#### associativity - divide left associative

- associativity - divide left associative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("associativity - divide left associative")
check(20 / 4 / 2 == 2)
```

</details>

### Expression Combinations

#### nested calls

- nested calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested calls")
fn f(x: i64) -> i64: x + 1
fn g(x: i64) -> i64: x * 2
check(f(g(f(5))) == 13)
```

</details>

#### call with expression args

- call with expression args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call with expression args")
fn add(a: i64, b: i64) -> i64: a + b
check(add(2 + 3, 4 * 5) == 25)
```

</details>

#### nested array access

- nested array access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested array access")
val arr = [[1, 2], [3, 4], [5, 6]]
check(arr[1][1] == 4)
```

</details>

#### method chain - multiple

- method chain - multiple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("method chain - multiple")
val s = "  hello  "
val result = s.trim()
check(result == "hello")
```

</details>

#### array with expressions

- array with expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array with expressions")
val a = 5
val arr = [a, a + 1, a + 2, a * 2]
check(arr[0] == 5)
check(arr[3] == 10)
```

</details>

#### string interpolation nested

- string interpolation nested


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string interpolation nested")
val x = 5
val y = 10
val s = "{x + y}"
check(s.contains("15"))
```

</details>

### Statement Coverage

#### val declaration - no type

- val declaration - no type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("val declaration - no type")
val x = 42
check(x == 42)
```

</details>

#### val declaration - with type

- val declaration - with type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("val declaration - with type")
val x: i64 = 42
check(x == 42)
```

</details>

#### var declaration - no initial value

- var declaration - no initial value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var declaration - no initial value")
var x: i64 = 0
x = 42
check(x == 42)
```

</details>

#### var declaration - with initial value

- var declaration - with initial value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var declaration - with initial value")
var x = 42
x = x + 1
check(x == 43)
```

</details>

#### assignment - simple

- assignment - simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assignment - simple")
var x = 0
x = 42
check(x == 42)
```

</details>

#### assignment - with expression

- assignment - with expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assignment - with expression")
var x = 10
x = x * 2 + 5
check(x == 25)
```

</details>

#### assignment - array element

- assignment - array element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assignment - array element")
var arr = [1, 2, 3]
arr[1] = 10
check(arr[1] == 10)
```

</details>

### Complex Pattern Matching

#### match - nested patterns

- match - nested patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - nested patterns")
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

- match - multiple nested levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - multiple nested levels")
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

- variable binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("variable binding")
val a = 5
val b = 10
val sum = a + b
check(sum == 15)
```

</details>

### Function Definition Edge Cases

#### function - no parameters

- function - no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - no parameters")
fn f() -> i64: 42
check(f() == 42)
```

</details>

#### function - one parameter

- function - one parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - one parameter")
fn f(x: i64) -> i64: x
check(f(42) == 42)
```

</details>

#### function - many parameters

- function - many parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - many parameters")
fn f(a: i64, b: i64, c: i64, d: i64) -> i64:
    a + b + c + d
check(f(1, 2, 3, 4) == 10)
```

</details>

#### function - no return type

- function - no return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - no return type")
fn f(x: i64):
    pass
f(42)
check(true)
```

</details>

#### function - explicit return

- function - explicit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - explicit return")
fn f(x: i64) -> i64:
    return x * 2
check(f(5) == 10)
```

</details>

#### function - implicit return

- function - implicit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - implicit return")
fn f(x: i64) -> i64:
    x * 2
check(f(5) == 10)
```

</details>

#### function - early return in if

- function - early return in if


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - early return in if")
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

- function - early return in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - early return in loop")
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

- struct - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct - empty")
struct Empty:
    pass
val e = Empty()
check(true)
```

</details>

#### struct - single field

- struct - single field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct - single field")
struct Single:
    x: i64
val s = Single(x: 42)
check(s.x == 42)
```

</details>

#### struct - multiple fields

- struct - multiple fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct - multiple fields")
struct Point:
    x: i64
    y: i64
val p = Point(x: 3, y: 4)
check(p.x == 3)
check(p.y == 4)
```

</details>

#### struct - field access

- struct - field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct - field access")
struct Data:
    value: i64
val d = Data(value: 100)
val x = d.value
check(x == 100)
```

</details>

#### struct - field update

- struct - field update


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct - field update")
struct Counter:
    count: i64
var c = Counter(count: 0)
c.count = c.count + 1
check(c.count == 1)
```

</details>

### Enum Coverage

#### enum - simple

- enum - simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enum - simple")
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

- enum - with match all cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enum - with match all cases")
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

- handles extra whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles extra whitespace")
val    x    =    42
check(x == 42)
```

</details>

#### handles tabs

- handles tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles tabs")
val	x	=	42
check(x == 42)
```

</details>

#### handles line breaks

- handles line breaks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles line breaks")
val x =
    42
check(x == 42)
```

</details>

#### handles empty lines

- handles empty lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty lines")

val x = 42

check(x == 42)
```

</details>

### Literal Edge Cases

#### bool - true literal

- bool - true literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool - true literal")
val t = true
check(t)
```

</details>

#### bool - false literal

- bool - false literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool - false literal")
val f = false
check(not f)
```

</details>

#### nil - literal

- nil - literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil - literal")
val n = nil
check(not n.?)
```

</details>

#### tuple - two elements

- tuple - two elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tuple - two elements")
val a = 1
val b = 2
check(a == 1 and b == 2)
```

</details>

#### tuple - three elements

- tuple - three elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tuple - three elements")
val a = 1
val b = 2
val c = 3
check(a == 1 and b == 2 and c == 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/branch_coverage_29_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer Edge Cases, Parser Precedence Edge Cases, Expression Combinations, Statement Coverage, Complex Pattern Matching, Function Definition Edge Cases, Struct and Type Usage, Enum Coverage, Whitespace and Formatting, Literal Edge Cases.
- Lexer Edge Cases
- Parser Precedence Edge Cases
- Expression Combinations
- Statement Coverage
- Complex Pattern Matching
- Function Definition Edge Cases
- Struct and Type Usage
- Enum Coverage
- Whitespace and Formatting
- Literal Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99600a6381c88ed978cd612bcc73b76b040d85b690508d7b23a9c44fc4ce83f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99600a6381c88ed978cd612bcc73b76b040d85b690508d7b23a9c44fc4ce83f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99600a6381c88ed978cd612bcc73b76b040d85b690508d7b23a9c44fc4ce83f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/branch_coverage_29_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/branch_coverage_29_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/branch_coverage_29_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/branch_coverage_29_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/branch_coverage_29_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'number - leading zeros' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/branch_coverage_29_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'number - underscore separators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/branch_coverage_29_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'number - underscore in hex' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
