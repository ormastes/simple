# Line Continuation Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Line Continuation Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2400 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/line_continuation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Explicit continuation with backslash
use std.spec.step

val sum = value1 + \
value2 + \
value3

# Function call with continuation
val result = add(1, \
2, \
3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Explicit Continuation | Backslash at line end forces continuation to next line |
| Nesting | Multiple levels of continuation allowed |
| Indentation | Improves readability but not required for continuation |

## Behavior

Line continuation:
- Backslash at end of line continues expression to next line
- Multiple continuations can be chained
- Works in expressions and function calls
- Preserves semantic meaning across line boundaries

## Note

Implicit continuation (just newlines inside parentheses/brackets/braces) is not
currently supported. Use explicit backslash continuation instead.

## Scenarios

### Line Continuation

#### explicit continuation with backslash

#### continues expression with backslash

- continues expression with backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues expression with backslash")
val result = 1 + 2 + \
    3 + 4
expect result == 10
```

</details>

#### continues function call with backslash

- continues function call with backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues function call with backslash")
fn add(a, b, c):
    a + b + c
val result = add(1, \
    2, \
    3)
expect result == 6
```

</details>

#### combines backslash and arithmetic

- combines backslash and arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines backslash and arithmetic")
val a = 10
val b = 20
val c = 30
val result = a + \
    b + \
    c
expect result == 60
```

</details>

#### chains multiple continuations

- chains multiple continuations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple continuations")
val result = 1 + \
    2 + \
    3 + \
    4 + \
    5
expect result == 15
```

</details>

#### continuation in various expressions

#### continues binary operation

- continues binary operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues binary operation")
val x = 100 + \
    200
expect x == 300
```

</details>

#### continues comparison

- continues comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues comparison")
val a = 5
val b = 10
val result = a < \
    b
var r = 0
if result:
    r = 1
expect r == 1
```

</details>

#### continues string concatenation

- continues string concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues string concatenation")
val s = "Hello" + \
    " " + \
    "World"
var result = 0
if s == "Hello World":
    result = 1
expect result == 1
```

</details>

#### implicit trailing-operator continuation (no backslash)

#### continues a trailing greater-than into the next line

- continues a trailing greater-than into the next line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues a trailing greater-than into the next line")
val limit = 100
val slack = 10
val over = 200 >
    limit - slack
expect over == true
```

</details>

#### continues a trailing equality into the next line

- continues a trailing equality into the next line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues a trailing equality into the next line")
val left = 7
val same = left ==
    7
expect same == true
```

</details>

#### continues a trailing comparison inside an if condition

- continues a trailing comparison inside an if condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues a trailing comparison inside an if condition")
val size = 200
val cap = 100
var hit = 0
if size >
   cap - 10:
    hit = 1
expect hit == 1
```

</details>

#### continues a trailing comparison inside a while condition

- continues a trailing comparison inside a while condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues a trailing comparison inside a while condition")
var n = 0
var seen = 0
while n <
      3:
    seen = seen + 1
    n = n + 1
expect seen == 3
```

</details>

#### continuation with indentation

#### works with any indentation level

- works with any indentation level


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with any indentation level")
val result = 10 + \
            20 + \
    30
expect result == 60
```

</details>

#### continues deeply indented code

- continues deeply indented code


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues deeply indented code")
fn outer():
    fn inner():
        val x = 1 + \
            2
        return x
    return inner()
expect outer() == 3
```

</details>

#### practical examples

#### formats long arithmetic expression

- formats long arithmetic expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats long arithmetic expression")
val total = 100 + \
    200 + \
    300 + \
    400
expect total == 1000
```

</details>

#### formats function with many arguments

- formats function with many arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats function with many arguments")
fn sum5(a, b, c, d, e):
    a + b + c + d + e
val result = sum5(1, \
    2, \
    3, \
    4, \
    5)
expect result == 15
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `1f33d5967c1c6d193300b0d0db5b9e20a0ad1c76cbbc058e7671b99c85970e06`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f33d5967c1c6d193300b0d0db5b9e20a0ad1c76cbbc058e7671b99c85970e06`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f33d5967c1c6d193300b0d0db5b9e20a0ad1c76cbbc058e7671b99c85970e06`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/line_continuation_spec.spl
mirror: doc/06_spec/03_system/feature/usage/line_continuation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/line_continuation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/line_continuation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/line_continuation_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'continues expression with backslash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/line_continuation_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'continues function call with backslash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/line_continuation_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'combines backslash and arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
