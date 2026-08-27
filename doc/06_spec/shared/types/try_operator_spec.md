# Try Operator Specification

> Tests covering Try operator (?).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Try Operator Specification

## Scenarios

### Try operator (?)

#### with Result type

#### unwraps Ok values

- unwraps Ok values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("unwraps Ok values")
val result = divide(a=10, b=2)
expect result.is_ok() == true
expect result.unwrap() == 5
```

</details>

#### propagates Err on failure

- propagates Err on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("propagates Err on failure")
val result = compute_ratio(a=100, b=0, c=5)
expect result.is_err() == true
```

</details>

#### chains multiple ? operations

- chains multiple ? operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("chains multiple ? operations")
val result = compute_ratio(a=100, b=5, c=2)
# 100 / 5 = 20, 20 / 2 = 10
expect result.is_ok() == true
expect result.unwrap() == 10
```

</details>

#### stops at first error in chain

- stops at first error in chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("stops at first error in chain")
val result = safe_sqrt_ratio(a=10, b=0)
# First division fails
expect result.is_err() == true
```

</details>

#### handles negative sqrt error

- handles negative sqrt error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("handles negative sqrt error")
val result = safe_sqrt_ratio(a=-100, b=10)
# -100 / 10 = -10, sqrt(-10) fails
expect result.is_err() == true
```

</details>

#### completes successfully when all succeed

- completes successfully when all succeed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("completes successfully when all succeed")
val result = safe_sqrt_ratio(a=100, b=4)
# 100 / 4 = 25, sqrt(25) = 5
expect result.is_ok() == true
expect result.unwrap() == 5
```

</details>

#### with Option type

#### unwraps Some values

- unwraps Some values
   - Expected: is_some is true
   - Expected: unwrapped equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("unwraps Some values")
val arr = [10, 20, 30]
val result = find_value(arr, 20)
val is_some = result.is_some()
expect(is_some).to_equal(true)
val unwrapped = result.unwrap()
expect(unwrapped).to_equal(1)
```

</details>

#### propagates None on not found

- propagates None on not found
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("propagates None on not found")
val arr = [10, 20, 30]
val result = get_element(arr, 99)
val is_none = result.is_none()
expect(is_none).to_equal(true)
```

</details>

#### returns value when found

- returns value when found
   - Expected: is_some is true
   - Expected: unwrapped equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns value when found")
val arr = [10, 20, 30]
val result = get_element(arr, 20)
val is_some = result.is_some()
expect(is_some).to_equal(true)
val unwrapped = result.unwrap()
expect(unwrapped).to_equal(20)
```

</details>

#### early return behavior

#### returns immediately on Err

- returns immediately on Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns immediately on Err")
# This tests that code after ? doesn't execute on error
fn test_early_return(x: i64) -> Result<i64, text>:
    val result_val = divide(a=10, b=x)?
    # This line should not execute if x == 0
    return Ok(result_val * 1000)

val result = test_early_return(0)
expect result.is_err() == true
```

</details>

#### continues execution on Ok

- continues execution on Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("continues execution on Ok")
fn test_continue(x: i64) -> Result<i64, text>:
    val result_val = divide(a=10, b=x)?
    return Ok(result_val * 1000)

val result = test_continue(2)
expect result.is_ok() == true
expect result.unwrap() == 5000
```

</details>

#### nested function calls

#### propagates through call stack

- propagates through call stack
   - Expected: is_err2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("propagates through call stack")
fn inner(x: i64) -> Result<i64, text>:
    return divide(a=100, b=x)

fn middle(x: i64) -> Result<i64, text>:
    val inner_val = inner(x)?
    return Ok(inner_val + 1)

fn outer(x: i64) -> Result<i64, text>:
    val mid_val = middle(x)?
    return Ok(mid_val * 2)

# Success case: 100/5=20, 20+1=21, 21*2=42
val result = outer(5)
expect result.is_ok() == true
expect result.unwrap() == 42

# Failure case: division by zero propagates up
val result_fail = outer(0)
val is_err2 = result_fail.is_err()
expect(is_err2).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/try_operator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Try operator (?).
- Try operator (?)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `51923ee5e5a5cdd9277aaaab0a667c598eaf6d0c2954e1723fa29c4f98fce27d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51923ee5e5a5cdd9277aaaab0a667c598eaf6d0c2954e1723fa29c4f98fce27d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51923ee5e5a5cdd9277aaaab0a667c598eaf6d0c2954e1723fa29c4f98fce27d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/shared/types/try_operator_spec.spl
mirror: doc/06_spec/shared/types/try_operator_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/types/try_operator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/types/try_operator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/types/try_operator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/shared/types/try_operator_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps Ok values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/try_operator_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates Err on failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/try_operator_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains multiple ? operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
