# Inline Statement Specification

> Tests covering Inline statement in if, return statement, break statement, continue statement, combined with regular if.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Statement Specification

## Scenarios

### Inline statement in if

### return statement

#### supports inline return in function

- supports inline return in function


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline return in function")
fn get_value(x: i64) -> i64:
    if x < 0: return -1
    if x == 0: return 0
    return 1

expect get_value(-5) == -1
expect get_value(0) == 0
expect get_value(5) == 1
```

</details>

#### supports inline return with expression

- supports inline return with expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline return with expression")
fn abs_value(x: i64) -> i64:
    if x < 0: return -x
    return x

expect abs_value(-10) == 10
expect abs_value(10) == 10
expect abs_value(0) == 0
```

</details>

#### supports inline return in multiple conditions

- supports inline return in multiple conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline return in multiple conditions")
fn classify(x: i64) -> text:
    if x < 0: return "negative"
    if x == 0: return "zero"
    if x > 100: return "large"
    return "positive"

expect classify(-5) == "negative"
expect classify(0) == "zero"
expect classify(50) == "positive"
expect classify(200) == "large"
```

</details>

### break statement

<details>
<summary>Advanced: supports inline break in loop</summary>

#### supports inline break in loop

- supports inline break in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline break in loop")
var sum = 0
var i = 0
while i < 100:
    if i >= 5: break
    sum = sum + i
    i = i + 1

expect sum == 10  # 0+1+2+3+4 = 10
expect i == 5
```

</details>


</details>

<details>
<summary>Advanced: supports inline break in for loop</summary>

#### supports inline break in for loop

- supports inline break in for loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline break in for loop")
var count = 0
for x in [1, 2, 3, 4, 5]:
    if x > 3: break
    count = count + 1

expect count == 3
```

</details>


</details>

### continue statement

<details>
<summary>Advanced: supports inline continue in loop</summary>

#### supports inline continue in loop

- supports inline continue in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline continue in loop")
var sum = 0
for x in [1, 2, 3, 4, 5]:
    if x == 3: continue
    sum = sum + x

expect sum == 12  # 1+2+4+5 = 12
```

</details>


</details>

#### supports inline continue skipping multiple values

- supports inline continue skipping multiple values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports inline continue skipping multiple values")
var result = []
for x in [1, 2, 3, 4, 5, 6]:
    if x % 2 == 0: continue
    result = result.push(x)

expect result == [1, 3, 5]
```

</details>

### combined with regular if

#### works with elif and else blocks

- works with elif and else blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with elif and else blocks")
fn categorize(x: i64) -> text:
    if x < 0: return "negative"
    elif x == 0:
        return "zero"
    else:
        return "positive"

expect categorize(-1) == "negative"
expect categorize(0) == "zero"
expect categorize(1) == "positive"
```

</details>

#### allows inline if without else when using statement

- allows inline if without else when using statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows inline if without else when using statement")
fn early_return(x: i64) -> i64:
    if x < 0: return 0
    # This line is reached only for non-negative x
    return x * 2

expect early_return(-5) == 0
expect early_return(5) == 10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/inline_statement_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Inline statement in if, return statement, break statement, continue statement, combined with regular if.
- Inline statement in if
- return statement
- break statement
- continue statement
- combined with regular if

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `84eee8c716461433a13ccba1921fd2d6165be3ffda1dc5347be0722f8c4be172`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84eee8c716461433a13ccba1921fd2d6165be3ffda1dc5347be0722f8c4be172`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84eee8c716461433a13ccba1921fd2d6165be3ffda1dc5347be0722f8c4be172`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/inline_statement_spec.spl
mirror: doc/06_spec/01_unit/lib/common/inline_statement_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/inline_statement_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/inline_statement_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/inline_statement_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports inline return in function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/inline_statement_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports inline return with expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/inline_statement_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports inline return in multiple conditions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
