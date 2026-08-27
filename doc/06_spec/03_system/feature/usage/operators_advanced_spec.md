# Advanced Operators Specification

> let x = 10       # immutable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Operators Specification

let x = 10       # immutable

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OP-ADV-001 to #OP-ADV-030 |
| Category | Language \| Operators |
| Status | Implemented |
| Source | `test/03_system/feature/usage/operators_advanced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Mutability
let x = 10       # immutable
let mut y = 10   # mutable with let mut
var z = 10       # mutable with var
use std.spec.step

const MAX = 100  # constant
static counter = 0  # static variable

# Operators
val a = 12 & 10    # bitwise AND
val b = 2 ** 10    # power
val c = 7.fdiv(2)  # floor division (// is now parallel operator)
val d = "ell" in "hello"  # in operator
```

## Scenarios

### Mutability Control

#### let is immutable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- let is immutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("let is immutable")
val x = 10
# x = 20  # Would be error
expect x == 10
```

</details>

#### var is mutable

- var is mutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("var is mutable")
var y = 10
y = 30
expect y == 30
```

</details>

<details>
<summary>Advanced: var in loop</summary>

#### var in loop

- var in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("var in loop")
var sum = 0
var i = 0
while i < 5:
    sum = sum + i
    i = i + 1
expect sum == 10  # 0+1+2+3+4
```

</details>


</details>

#### const declaration

- const declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("const declaration")
const MAX = 100
expect MAX == 100
```

</details>

#### const with arithmetic

- const with arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("const with arithmetic")
const BASE = 10
const MULTIPLIER = 5
expect BASE * MULTIPLIER == 50
```

</details>

#### const with type annotation

- const with type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("const with type annotation")
const SIZE: i64 = 256
expect SIZE == 256
```

</details>

#### static variable

- static variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("static variable")
static counter = 42
expect counter == 42
```

</details>

### Lambda Expressions

#### basic lambda

- basic lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("basic lambda")
val double = \x: x * 2
expect double(21) == 42
```

</details>

#### lambda with multiple params

- lambda with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda with multiple params")
val add = \a, b: a + b
expect add(10, 32) == 42
```

</details>

#### lambda as higher-order

- lambda as higher-order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda as higher-order")
fn apply(f, x):
    f(x)

val inc = \n: n + 1
expect apply(inc, 41) == 42
```

</details>

### String Operations

#### string length

- string length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string length")
val s = "hello"
expect s.len() == 5
```

</details>

#### string concatenation

- string concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string concatenation")
val a = "hello"
val b = "world"
val c = a + " " + b
expect c.len() == 11
```

</details>

#### string interpolation

- string interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string interpolation")
val x = 42
val s = "value is {x}"
expect s.len() == 11
```

</details>

### Array Methods

#### array length

- array length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array length")
val arr = [1, 2, 3, 4, 5]
expect arr.len() == 5
```

</details>

### Dict Methods

#### dict length

- dict length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dict length")
val d = {"a": 1, "b": 2, "c": 3}
expect d.len() == 3
```

</details>

#### dict keys

- dict keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dict keys")
val d = {"x": 10, "y": 20}
val keys = d.keys()
expect keys.len() == 2
```

</details>

#### dict values

- dict values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dict values")
val d = {"a": 5, "b": 10}
val vals = d.values()
expect vals[0] + vals[1] == 15
```

</details>

#### dict contains_key

- dict contains_key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dict contains_key")
val d = {"hello": 1}
expect d.has("hello")
```

</details>

### Bitwise Operators

#### bitwise AND

- bitwise AND


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise AND")
expect (12 & 10) == 8  # 1100 & 1010 = 1000
```

</details>

#### bitwise OR

- bitwise OR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise OR")
expect (12 | 10) == 14  # 1100 | 1010 = 1110
```

</details>

#### bitwise XOR

- bitwise XOR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise XOR")
expect (12 xor 10) == 6  # 1100 ^ 1010 = 0110
```

</details>

#### left shift

- left shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("left shift")
expect (1 << 4) == 16
```

</details>

#### right shift

- right shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("right shift")
expect (16 >> 2) == 4
```

</details>

#### bitwise NOT

- bitwise NOT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise NOT")
expect (~0) == -1
```

</details>

### Comparison Operators

#### less than

- less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than")
expect 1 < 2
```

</details>

#### greater than

- greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than")
expect 2 > 1
```

</details>

#### less than or equal

- less than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than or equal")
expect 2 <= 2
```

</details>

#### greater than or equal

- greater than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than or equal")
expect 2 >= 2
```

</details>

#### equal

- equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("equal")
expect 2 == 2
```

</details>

#### not equal

- not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not equal")
expect 2 != 3
```

</details>

### Logical Operators

#### and operator

- and operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("and operator")
expect true and true
expect not (true and false)
```

</details>

#### or operator

- or operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or operator")
expect true or false
expect not (false or false)
```

</details>

#### not operator

- not operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not operator")
expect not false
expect not (not true)
```

</details>

### Power Operator

#### power of zero

- power of zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("power of zero")
expect (2 ** 0) == 1
```

</details>

#### power of one

- power of one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("power of one")
expect (2 ** 1) == 2
```

</details>

#### power of three

- power of three


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("power of three")
expect (2 ** 3) == 8
```

</details>

#### power of ten

- power of ten


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("power of ten")
expect (2 ** 10) == 1024
```

</details>

#### three to fourth

- three to fourth


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("three to fourth")
expect (3 ** 4) == 81
```

</details>

### Floor Division

#### positive floor division

- positive floor division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("positive floor division")
expect 7.fdiv(2) == 3
```

</details>

#### another floor division

- another floor division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("another floor division")
expect 10.fdiv(3) == 3
```

</details>

#### negative floor division

- negative floor division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negative floor division")
expect (-7).fdiv(2) == -4  # rounds toward negative infinity
```

</details>

#### exact division

- exact division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exact division")
expect 8.fdiv(4) == 2
```

</details>

### In Operator

#### in array present

- in array present


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("in array present")
expect 2 in [1, 2, 3]
```

</details>

#### in array absent

- in array absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("in array absent")
expect not (5 in [1, 2, 3])
```

</details>

#### in string present

- in string present


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("in string present")
expect "ell" in "hello"
```

</details>

#### in string absent

- in string absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("in string absent")
expect not ("xyz" in "hello")
```

</details>

### Recursive Functions

#### factorial

- factorial


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("factorial")
fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

expect factorial(3) == 6
```

</details>

### Nested Data Structures

#### nested arrays

- nested arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested arrays")
val arr = [[1, 2], [3, 4], [5, 6]]
expect arr[0][0] + arr[1][1] + arr[2][0] == 10
```

</details>

#### nested structs

- nested structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested structs")
struct Inner:
    value: i64

struct Outer:
    inner: Inner

val o = Outer(inner: Inner(value: 42))
expect o.inner.value == 42
```

</details>

### Early Return

#### early return based on condition

- early return based on condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("early return based on condition")
fn verify(x: i64) -> i64:
    if x > 10:
        return 1
    if x > 5:
        return 2
    3

expect verify(7) == 2
```

</details>

### Tuple Destructuring

#### destructures tuple

- destructures tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures tuple")
val _tuple = (1, 2, 3)
val a = _tuple[0]
val b = _tuple[1]
val c = _tuple[2]
expect a + b + c == 6
```

</details>

### Symbols

#### symbol comparison

- symbol comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("symbol comparison")
val s = :hello
expect s == :hello
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
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

- Canonical SPipe generation for source `244ce4a95574826b2b8090da06ee27d2c9284d08e2d88cfe56ce811fd1a62b99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `244ce4a95574826b2b8090da06ee27d2c9284d08e2d88cfe56ce811fd1a62b99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `244ce4a95574826b2b8090da06ee27d2c9284d08e2d88cfe56ce811fd1a62b99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/operators_advanced_spec.spl
mirror: doc/06_spec/03_system/feature/usage/operators_advanced_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/operators_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/operators_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/operators_advanced_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'let is immutable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/operators_advanced_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var is mutable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/operators_advanced_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var in loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
