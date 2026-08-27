# If Else Implicit Return Specification

> Tests covering If-else implicit return, basic if-else, if-elif-else chain, nested if-else, with other statements before, return type inference, mixed with explicit return, with function calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# If Else Implicit Return Specification

## Scenarios

### If-else implicit return

### basic if-else

#### returns value from if branch

- returns value from if branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns value from if branch")
fn get_sign(x: i64) -> text:
    if x >= 0:
        "positive"
    else:
        "negative"

expect get_sign(5) == "positive"
expect get_sign(-5) == "negative"
```

</details>

#### returns value from else branch

- returns value from else branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns value from else branch")
fn is_even(x: i64) -> bool:
    if x % 2 == 0:
        true
    else:
        false

expect is_even(4) == true
expect is_even(3) == false
```

</details>

#### returns complex expressions

- returns complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns complex expressions")
fn double_or_triple(x: i64, double: bool) -> i64:
    if double:
        x * 2
    else:
        x * 3

expect double_or_triple(5, true) == 10
expect double_or_triple(5, false) == 15
```

</details>

### if-elif-else chain

#### returns from elif branch

- returns from elif branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns from elif branch")
fn classify(x: i64) -> text:
    if x < 0:
        "negative"
    elif x == 0:
        "zero"
    else:
        "positive"

expect classify(-5) == "negative"
expect classify(0) == "zero"
expect classify(5) == "positive"
```

</details>

#### returns from multiple elif branches

- returns from multiple elif branches


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns from multiple elif branches")
fn grade(score: i64) -> text:
    if score >= 90:
        "A"
    elif score >= 80:
        "B"
    elif score >= 70:
        "C"
    elif score >= 60:
        "D"
    else:
        "F"

expect grade(95) == "A"
expect grade(85) == "B"
expect grade(75) == "C"
expect grade(65) == "D"
expect grade(55) == "F"
```

</details>

### nested if-else

#### returns from nested if-else

- returns from nested if-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns from nested if-else")
fn nested_check(a: bool, b: bool) -> text:
    if a:
        if b:
            "both"
        else:
            "only a"
    else:
        if b:
            "only b"
        else:
            "neither"

expect nested_check(true, true) == "both"
expect nested_check(true, false) == "only a"
expect nested_check(false, true) == "only b"
expect nested_check(false, false) == "neither"
```

</details>

### with other statements before

#### returns after variable declaration

- returns after variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns after variable declaration")
fn add_with_check(a: i64, b: i64) -> i64:
    val sum = a + b
    if sum > 100:
        100
    else:
        sum

expect add_with_check(30, 40) == 70
expect add_with_check(80, 50) == 100
```

</details>

<details>
<summary>Advanced: returns after loop</summary>

#### returns after loop

- returns after loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns after loop")
fn sum_until(limit: i64) -> i64:
    var total = 0
    var i = 1
    while i <= limit:
        total = total + i
        i = i + 1
    if total > 100:
        100
    else:
        total

expect sum_until(5) == 15
expect sum_until(20) == 100
```

</details>


</details>

### return type inference

#### works with integer return

- works with integer return


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with integer return")
fn max_val(a: i64, b: i64) -> i64:
    if a > b:
        a
    else:
        b

expect max_val(10, 5) == 10
expect max_val(5, 10) == 10
```

</details>

#### works with text return

- works with text return


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with text return")
fn greeting(formal: bool) -> text:
    if formal:
        "Good day"
    else:
        "Hi"

expect greeting(true) == "Good day"
expect greeting(false) == "Hi"
```

</details>

#### works with boolean return

- works with boolean return


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with boolean return")
fn both_positive(a: i64, b: i64) -> bool:
    if a > 0 and b > 0:
        true
    else:
        false

expect both_positive(1, 2) == true
expect both_positive(-1, 2) == false
```

</details>

### mixed with explicit return

#### works with early return and implicit else

- works with early return and implicit else


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with early return and implicit else")
fn absolute(x: i64) -> i64:
    if x < 0:
        return -x
    x

expect absolute(-5) == 5
expect absolute(5) == 5
```

</details>

#### works with guard clause pattern

- works with guard clause pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with guard clause pattern")
fn safe_divide(a: i64, b: i64) -> i64:
    if b == 0:
        return 0
    if a < 0:
        -1
    else:
        a / b

expect safe_divide(10, 2) == 5
expect safe_divide(10, 0) == 0
expect safe_divide(-10, 2) == -1
```

</details>

### with function calls

#### returns function call result

- returns function call result


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns function call result")
fn double(x: i64) -> i64:
    x * 2

fn conditional_double(x: i64, should_double: bool) -> i64:
    if should_double:
        double(x)
    else:
        x

expect conditional_double(5, true) == 10
expect conditional_double(5, false) == 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/if_else_implicit_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering If-else implicit return, basic if-else, if-elif-else chain, nested if-else, with other statements before, return type inference, mixed with explicit return, with function calls.
- If-else implicit return
- basic if-else
- if-elif-else chain
- nested if-else
- with other statements before
- return type inference
- mixed with explicit return
- with function calls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7aaca9acf1331c5e9ae821bbebe0e62c6c0df23a8aa9ed1f049f2aea2464a157`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7aaca9acf1331c5e9ae821bbebe0e62c6c0df23a8aa9ed1f049f2aea2464a157`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7aaca9acf1331c5e9ae821bbebe0e62c6c0df23a8aa9ed1f049f2aea2464a157`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/control_flow/if_else_implicit_return_spec.spl
mirror: doc/06_spec/shared/control_flow/if_else_implicit_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/control_flow/if_else_implicit_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/control_flow/if_else_implicit_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/control_flow/if_else_implicit_return_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value from if branch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/if_else_implicit_return_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value from else branch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/if_else_implicit_return_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns complex expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
