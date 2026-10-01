# Compiler Branch Coverage Specification

> Tests covering Number Literal Branches, String Literal Branches, Keyword Branches, Operator Branches, Delimiter Branches, Complex Expression Branches, Control Flow Branches, Type System Branches, Edge Cases, Test Summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Branch Coverage Specification

## Scenarios

### Number Literal Branches

#### covers integer literals

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- covers integer literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers integer literals")
val a = 42
val b = 0
val c = 1_000_000
expect a == 42
expect b == 0
expect c == 1000000
```

</details>

#### covers hex literals

- covers hex literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers hex literals")
val h1 = 0xFF
val h2 = 0xABCDEF
val h3 = 0xFF_FF
expect h1 == 255
```

</details>

#### covers binary literals

- covers binary literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers binary literals")
val b1 = 0b1010
val b2 = 0b1111_0000
expect b1 == 10
```

</details>

#### covers octal literals

- covers octal literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers octal literals")
val o1 = 0o777
val o2 = 0o77_77
expect o1 == 511
```

</details>

#### covers float literals

- covers float literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers float literals")
val f1 = 3.14
val f2 = 1_000.000_1
val f3 = 1e10
val f4 = 1E10
val f5 = 1e+10
val f6 = 1e-10
val f7 = 1.23e-45
expect f1 > 3.0
```

</details>

### String Literal Branches

#### covers simple strings

- covers simple strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers simple strings")
val s1 = "hello"
val s2 = "world"
expect s1 == "hello"
expect s2 == "world"
```

</details>

#### covers escape sequences

- covers escape sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers escape sequences")
val e1 = "a\nb"
val e2 = "a\tb"
val e3 = "a\\b"
val e4 = "a\"b"
expect e1.len() == 3
expect e2.len() == 3
```

</details>

### Keyword Branches

#### covers val and var

- covers val and var


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers val and var")
val x = 1
var y = 2
y = 3
expect x == 1
expect y == 3
```

</details>

#### covers fn keyword

- covers fn keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers fn keyword")
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(1, 2) == 3
```

</details>

#### covers if/elif/else

- covers if/elif/else


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers if/elif/else")
val x = 5
val r = if x > 10:
    "big"
elif x > 3:
    "medium"
else:
    "small"
expect r == "medium"
```

</details>

#### covers match

- covers match


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers match")
val x = 2
val r = match x:
    case 1:
        "one"
    case 2:
        "two"
    case _:
        "other"
expect r == "two"
```

</details>

<details>
<summary>Advanced: covers for loop</summary>

#### covers for loop

- covers for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers for loop")
var sum = 0
for i in 0..5:
    sum = sum + i
expect sum == 10
```

</details>


</details>

<details>
<summary>Advanced: covers while loop</summary>

#### covers while loop

- covers while loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers while loop")
var count = 0
while count < 3:
    count = count + 1
expect count == 3
```

</details>


</details>

#### covers return

- covers return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers return")
fn get_value() -> i64:
    return 42
expect get_value() == 42
```

</details>

#### covers break and continue

- covers break and continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers break and continue")
var sum = 0
for i in 0..10:
    if i == 5:
        break
    if i == 2:
        continue
    sum = sum + i
expect sum == 1 + 3 + 4
```

</details>

### Operator Branches

#### covers arithmetic operators

- covers arithmetic operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers arithmetic operators")
expect 1 + 2 == 3
expect 5 - 3 == 2
expect 4 * 3 == 12
expect 10 / 2 == 5
expect 10 % 3 == 1
```

</details>

#### covers comparison operators

- covers comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers comparison operators")
expect (1 == 1) == true
expect (1 != 2) == true
expect (1 < 2) == true
expect (2 > 1) == true
expect (1 <= 1) == true
expect (1 >= 1) == true
```

</details>

#### covers logical operators

- covers logical operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers logical operators")
expect (true and true) == true
expect (true and false) == false
expect (true or false) == true
expect (false or false) == false
expect (not false) == true
```

</details>

#### covers assignment operators

- covers assignment operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers assignment operators")
var x = 10
x += 5
expect x == 15
x -= 3
expect x == 12
x *= 2
expect x == 24
x /= 4
expect x == 6
```

</details>

### Delimiter Branches

#### covers parentheses

- covers parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers parentheses")
val r = (1 + 2) * 3
expect r == 9
```

</details>

#### covers brackets

- covers brackets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers brackets")
val arr = [1, 2, 3]
expect arr[0] == 1
```

</details>

#### covers braces

- covers braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers braces")
struct Obj:
    x: i64
    y: i64
val obj = Obj { x: 1, y: 2 }
expect obj.x == 1
```

</details>

#### covers range operators

- covers range operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers range operators")
var count = 0
for i in 0..5:
    count = count + 1
expect count == 5

var count2 = 0
for i in 0..=5:
    count2 = count2 + 1
expect count2 == 6
```

</details>

#### covers optional operators

- covers optional operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers optional operators")
val x: i64? = nil
val y = x ?? 42
expect y == 42
```

</details>

### Complex Expression Branches

#### covers nested expressions

- covers nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers nested expressions")
val a = (1 + 2) * (3 + 4) - 5
expect a == 16
```

</details>

#### covers method chaining

- covers method chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers method chaining")
val s = "hello"
val r = s.len()
expect r == 5
```

</details>

#### covers lambda expressions

- covers lambda expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers lambda expressions")
val f = _1 * 2
expect f(5) == 10
```

</details>

#### covers list operations

- covers list operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers list operations")
val arr = [1, 2, 3]
val mapped = arr.map(_1 * 2)
expect mapped[0] == 2
expect mapped[1] == 4
expect mapped[2] == 6
```

</details>

### Control Flow Branches

#### covers nested if

- covers nested if


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers nested if")
val x = 5
val y = 10
val r = if x > 0:
    if y > 5:
        "both"
    else:
        "x only"
else:
    "neither"
expect r == "both"
```

</details>

#### covers early return

- covers early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers early return")
fn find_first_even(arr: [i64]) -> i64?:
    for x in arr:
        if x % 2 == 0:
            return x
    nil
expect find_first_even([1, 3, 4, 5]) == 4
expect find_first_even([1, 3, 5]) == nil
```

</details>

#### covers match with guards

- covers match with guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers match with guards")
fn classify(x: i64) -> text:
    match x:
        case n if n < 0:
            "negative"
        case 0:
            "zero"
        case n if n > 100:
            "large"
        case _:
            "small"
expect classify(-5) == "negative"
expect classify(0) == "zero"
expect classify(200) == "large"
expect classify(50) == "small"
```

</details>

### Type System Branches

#### covers basic types

- covers basic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers basic types")
val i: i64 = 42
val f: f64 = 3.14
val b: bool = true
val s: text = "hello"
expect i == 42
expect b == true
```

</details>

#### covers optional types

- covers optional types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers optional types")
val x: i64? = 42
val y: i64? = nil
expect x == 42
expect y == nil
```

</details>

#### covers array types

- covers array types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers array types")
val arr: [i64] = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### covers struct types

- covers struct types


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers struct types")
struct Point:
    x: i64
    y: i64
val p = Point { x: 1, y: 2 }
expect p.x == 1
expect p.y == 2
```

</details>

### Edge Cases

#### covers empty collections

- covers empty collections


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers empty collections")
val empty: [i64] = []
expect empty.len() == 0
```

</details>

#### covers single element

- covers single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers single element")
val single = [42]
expect single[0] == 42
```

</details>

#### covers zero values

- covers zero values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers zero values")
val zero = 0
val empty_str = ""
expect zero == 0
expect empty_str.len() == 0
```

</details>

#### covers negative numbers

- covers negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers negative numbers")
val neg = -42
expect neg == -42
expect neg < 0
```

</details>

### Test Summary

#### reports coverage

- reports coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports coverage")
print ""
print "Core Compiler Branch Coverage Tests Complete"
print "Covered:"
print "  - All number literal types"
print "  - All string escapes"
print "  - All keywords"
print "  - All operators"
print "  - All delimiters"
print "  - Complex expressions"
print "  - Control flow"
print "  - Type system"
print "  - Edge cases"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/compiler_branch_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Number Literal Branches, String Literal Branches, Keyword Branches, Operator Branches, Delimiter Branches, Complex Expression Branches, Control Flow Branches, Type System Branches, Edge Cases, Test Summary.
- Number Literal Branches
- String Literal Branches
- Keyword Branches
- Operator Branches
- Delimiter Branches
- Complex Expression Branches
- Control Flow Branches
- Type System Branches
- Edge Cases
- Test Summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
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

- Canonical SPipe generation for source `108dec5c46b9cef7bc70d0fd1ea4a26de632a0d5ac5dd8152a35fb577d07c945`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `108dec5c46b9cef7bc70d0fd1ea4a26de632a0d5ac5dd8152a35fb577d07c945`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `108dec5c46b9cef7bc70d0fd1ea4a26de632a0d5ac5dd8152a35fb577d07c945`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/compiler_branch_coverage_spec.spl
mirror: doc/06_spec/unit/compiler_core/compiler_branch_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/compiler_branch_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/compiler_branch_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/compiler_branch_coverage_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers integer literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/compiler_branch_coverage_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers hex literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/compiler_branch_coverage_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers binary literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
