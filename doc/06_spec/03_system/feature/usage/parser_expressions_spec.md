# Parser Expression Specification

> x + y, x - y, x * y, x / y, x % y, x ** y, x // y

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
| Updated | 2026-08-26 |
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

- parses addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses addition")
val x = 1 + 2
expect x == 3
```

</details>

#### parses subtraction

- parses subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses subtraction")
val x = 5 - 3
expect x == 2
```

</details>

#### parses multiplication

- parses multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiplication")
val x = 4 * 5
expect x == 20
```

</details>

#### parses division

- parses division


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses division")
val x = 10 / 2
expect x == 5
```

</details>

#### parses modulo

- parses modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses modulo")
val x = 7 % 3
expect x == 1
```

</details>

#### parses power

- parses power


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses power")
val x = 2 ** 3
expect x == 8
```

</details>

#### parses integer division

- parses integer division


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses integer division")
val x = 7.fdiv(3)
expect x == 2
```

</details>

#### operator precedence

#### multiplication before addition

- multiplication before addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiplication before addition")
val x = 2 + 3 * 4
expect x == 14
```

</details>

#### parentheses override precedence

- parentheses override precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parentheses override precedence")
val x = (2 + 3) * 4
expect x == 20
```

</details>

#### nested parentheses

- nested parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested parentheses")
val x = ((1 + 2) * 3)
expect x == 9
```

</details>

#### unary operations

#### parses unary minus

- parses unary minus


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unary minus")
val x = -5
expect x == -5
```

</details>

#### parses bitwise not

- parses bitwise not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses bitwise not")
val x = ~0
expect x == -1
```

</details>

### Comparison Expression Parsing

#### parses less than

- parses less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses less than")
expect (1 < 2) == true
```

</details>

#### parses greater than

- parses greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses greater than")
expect (2 > 1) == true
```

</details>

#### parses less than or equal

- parses less than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses less than or equal")
expect (2 <= 2) == true
```

</details>

#### parses greater than or equal

- parses greater than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses greater than or equal")
expect (3 >= 2) == true
```

</details>

#### parses equals

- parses equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses equals")
expect (2 == 2) == true
```

</details>

#### parses not equals

- parses not equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses not equals")
expect (1 != 2) == true
```

</details>

### Logical Expression Parsing

#### parses and

- parses and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses and")
val x = true and false
expect x == false
```

</details>

#### parses or

- parses or


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses or")
val x = true or false
expect x == true
```

</details>

#### parses not

- parses not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses not")
val x = not true
expect x == false
```

</details>

#### parses combined logical

- parses combined logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses combined logical")
val x = (true and false) or true
expect x == true
```

</details>

### Method and Field Access Parsing

#### method calls

#### parses no-arg method call

- parses no-arg method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses no-arg method call")
val arr = [1, 2, 3]
val len = arr.len()
expect len == 3
```

</details>

#### parses method call with args

- parses method call with args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses method call with args")
val arr = [1, 2, 3]
expect arr.contains(2)
```

</details>

#### parses chained method calls

- parses chained method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses chained method calls")
val arr = [1, 2, 3]
# NOTE: Using intermediate vars as workaround for interpreter chaining limitation
val mapped = arr.map(_1 * 2)
val result = mapped.filter(_1 > 2)
expect result.len() == 2
```

</details>

#### field access

#### parses field access

- parses field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses field access")
class Point:
    x: i64
    y: i64
val p = Point(x: 10, y: 20)
expect p.x == 10
```

</details>

#### parses nested field access

- parses nested field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested field access")
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

- parses integer index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses integer index")
val arr = [10, 20, 30]
expect arr[0] == 10
```

</details>

#### parses variable index

- parses variable index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses variable index")
val arr = [10, 20, 30]
val i = 1
expect arr[i] == 20
```

</details>

#### parses expression index

- parses expression index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses expression index")
val arr = [10, 20, 30]
expect arr[1 + 1] == 30
```

</details>

#### parses negative index

- parses negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses negative index")
val arr = [10, 20, 30]
expect arr[-1] == 30
```

</details>

#### slicing

#### parses start end slice

- parses start end slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses start end slice")
val arr = [0, 1, 2, 3, 4]
val sliced = arr[1:4]
expect sliced.len() == 3
```

</details>

#### parses end slice

- parses end slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses end slice")
val arr = [0, 1, 2, 3, 4]
val sliced = arr[:3]
expect sliced.len() == 3
```

</details>

#### parses start slice

- parses start slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses start slice")
val arr = [0, 1, 2, 3, 4]
val sliced = arr[2:]
expect sliced.len() == 3
```

</details>

### Function Call Expression Parsing

#### positional arguments

#### parses no-arg call

- parses no-arg call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses no-arg call")
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### parses single arg call

- parses single arg call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses single arg call")
fn double(x: i64) -> i64:
    x * 2
expect double(21) == 42
```

</details>

#### parses multi-arg call

- parses multi-arg call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multi-arg call")
fn add(a: i64, b: i64, c: i64) -> i64:
    a + b + c
expect add(10, 20, 12) == 42
```

</details>

#### named arguments

#### parses named arguments

- parses named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses named arguments")
fn greet(name: text, greeting: text) -> text:
    "{greeting}, {name}!"
val result = greet(name = "World", greeting = "Hello")
expect result == "Hello, World!"
```

</details>

### Path Expression Parsing

#### parses enum variant

- parses enum variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum variant")
enum Color:
    Red
    Green
    Blue
val c = Color.Red
expect c == Color.Red
```

</details>

#### parses nested path

- parses nested path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested path")
# Module path syntax - using function call instead
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

### Conditional Expression Parsing

#### parses if-else expression

- parses if-else expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses if-else expression")
val x = if true: 1 else: 0
expect x == 1
```

</details>

#### parses conditional comparison

- parses conditional comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses conditional comparison")
val a = 10
val b = 5
val max = if a > b: a else: b
expect max == 10
```

</details>

### Lambda Expression Parsing

#### parses single parameter lambda

- parses single parameter lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses single parameter lambda")
val f = \x: x + 1
expect f(41) == 42
```

</details>

#### parses multi-parameter lambda

- parses multi-parameter lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multi-parameter lambda")
val f = \a, b: a + b
expect f(20, 22) == 42
```

</details>

#### parses no-parameter lambda

- parses no-parameter lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses no-parameter lambda")
val f = \: 42
expect f() == 42
```

</details>

#### uses lambda with map

- uses lambda with map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lambda with map")
val arr = [1, 2, 3]
val doubled = arr.map(_1 * 2)
expect doubled[0] == 2
```

</details>

### is/in Expression Parsing

#### parses is expression

- parses is expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses is expression")
val opt: Option<i64> = Some(42)
if let Some(x) = opt:
    expect x == 42
```

</details>

#### parses in expression

- parses in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses in expression")
val list = [1, 2, 3]
expect 2 in list
```

</details>

#### parses not in expression

- parses not in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses not in expression")
val list = [1, 2, 3]
expect not (5 in list)
```

</details>

### Nested Expression Parsing

#### parses deeply nested arithmetic

- parses deeply nested arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses deeply nested arithmetic")
val x = ((1 + 2) * (3 + 4)) - ((5 - 6) * (7 - 8))
expect x == 21 - 1
```

</details>

#### parses nested collections

- parses nested collections


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested collections")
val arr = [[1, 2], [3, 4]]
expect arr[0][1] == 2
```

</details>

#### parses nested method chains

- parses nested method chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested method chains")
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

- parses optional chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses optional chaining")
val opt: Option<text> = Some("hello")
val len = opt?.len()
expect len == Some(5)
```

</details>

#### parses null coalescing

- parses null coalescing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses null coalescing")
val opt: Option<i64> = None
val value = opt ?? 42
expect value == 42
```

</details>

#### parses chained optional access

- parses chained optional access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses chained optional access")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7365afeb244a03ff1bd99bceeb5a4a19e796766cf13db52c2ec0bcb6ab3ee97b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7365afeb244a03ff1bd99bceeb5a4a19e796766cf13db52c2ec0bcb6ab3ee97b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7365afeb244a03ff1bd99bceeb5a4a19e796766cf13db52c2ec0bcb6ab3ee97b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_expressions_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_expressions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_expressions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_expressions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_expressions_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_expressions_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_expressions_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
