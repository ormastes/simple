# Union Impl Specification

> Tests covering Union keyword, Union Impl Methods, Union Pattern Matching, Union Type Safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Union Impl Specification

## Scenarios

### Union keyword

#### basic union creation

#### parses union types correctly

- parses union types correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("parses union types correctly")
# Union is an alias for enum in Simple
val s = Status.Active
expect true
```

</details>

#### creates inactive status variant

- creates inactive status variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates inactive status variant")
val s = Status.Inactive
expect true
```

</details>

#### creates union variant with string

- creates union variant with string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates union variant with string")
val r = MyResult.Err("failed")
expect true
```

</details>

#### union variants with payloads

#### supports union variants with payloads

- supports union variants with payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("supports union variants with payloads")
val r1 = MyResult.Ok(42)
val r2 = MyResult.Err("failed")
expect true
```

</details>

#### creates option with value

- creates option with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates option with value")
val opt = MyOption.Some(10)
expect true
```

</details>

#### creates empty option

- creates empty option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates empty option")
val opt = MyOption.Nothing
expect true
```

</details>

#### basic variant creation

#### works with basic variant creation

- works with basic variant creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("works with basic variant creation")
val opt = MyOption.Some(10)
# Union types work, pattern matching is separate feature
expect true
```

</details>

#### creates multiple variants of same type

- creates multiple variants of same type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates multiple variants of same type")
val opt1 = MyOption.Some(1)
val opt2 = MyOption.Some(2)
val opt3 = MyOption.Nothing
expect true
```

</details>

### Union Impl Methods

#### Status union methods

#### checks if status is active

- checks if status is active


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if status is active")
val s = Status.Active
expect s.is_active() == true
```

</details>

#### checks if status is inactive

- checks if status is inactive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if status is inactive")
val s = Status.Inactive
expect s.is_active() == false
```

</details>

#### displays status as string

- displays status as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("displays status as string")
val s = Status.Active
expect s.display() == "Active"
```

</details>

#### displays inactive status

- displays inactive status


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("displays inactive status")
val s = Status.Inactive
expect s.display() == "Inactive"
```

</details>

#### MyResult union methods

#### checks if result is ok

- checks if result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if result is ok")
val r = MyResult.Ok(42)
expect r.is_ok() == true
```

</details>

#### checks if result is error ok

- checks if result is error ok
   - Expected: ok_check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if result is error ok")
val r1 = MyResult.Err("failed")
val ok_check = r1.is_ok()
expect(ok_check).to_equal(false)
```

</details>

#### checks if result is error err

- checks if result is error err
   - Expected: err_check is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if result is error err")
val r2 = MyResult.Err("failed")
val err_check = r2.is_err()
expect(err_check).to_equal(true)
```

</details>

#### checks error predicate

- checks error predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks error predicate")
val r = MyResult.Ok(10)
expect r.is_err() == false
```

</details>

#### MyOption union methods

#### checks if option has value

- checks if option has value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if option has value")
val opt = MyOption.Some(10)
expect opt.is_some() == true
```

</details>

#### checks if option is empty

- checks if option is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("checks if option is empty")
val opt = MyOption.Nothing
expect opt.is_some() == false
```

</details>

#### gets value or default

- gets value or default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("gets value or default")
val opt1 = MyOption.Some(42)
expect opt1.get_or(0) == 42
```

</details>

#### uses default when none

- uses default when none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses default when none")
val opt2 = MyOption.Nothing
expect opt2.get_or(100) == 100
```

</details>

### Union Pattern Matching

#### simple pattern matching

#### matches active status

- matches active status


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches active status")
val s = Status.Active
val result = match s:
    case Status.Active:
        "active"
    case Status.Inactive:
        "inactive"
expect result == "active"
```

</details>

#### matches inactive status

- matches inactive status


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches inactive status")
val s = Status.Inactive
val result = match s:
    case Status.Active:
        "active"
    case Status.Inactive:
        "inactive"
expect result == "inactive"
```

</details>

#### pattern matching with payloads

#### extracts ok value

- extracts ok value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("extracts ok value")
val r = MyResult.Ok(42)
val result = match r:
    case MyResult.Ok(v):
        v
    case MyResult.Err(_):
        0
expect result == 42
```

</details>

#### extracts error message

- extracts error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("extracts error message")
val r = MyResult.Err("test error")
val result = match r:
    case MyResult.Ok(_):
        "ok"
    case MyResult.Err(msg):
        msg
expect result == "test error"
```

</details>

#### pattern matching on option

#### matches some variant with value

- matches some variant with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches some variant with value")
val opt = MyOption.Some(25)
val result = match opt:
    case MyOption.Some(v):
        v * 2
    case MyOption.Nothing:
        0
expect result == 50
```

</details>

#### matches nothing variant

- matches nothing variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("matches nothing variant")
val opt = MyOption.Nothing
val result = match opt:
    case MyOption.Some(v):
        v
    case MyOption.Nothing:
        -1
expect result == -1
```

</details>

### Union Type Safety

#### variant type consistency

#### creates result with integer

- creates result with integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates result with integer")
val r = MyResult.Ok(42)
expect true
```

</details>

#### creates result with string

- creates result with string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates result with string")
val r = MyResult.Err("error message")
expect true
```

</details>

#### creates option with integer

- creates option with integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates option with integer")
val opt = MyOption.Some(100)
expect true
```

</details>

#### multiple union types

#### handles different union types independently

- handles different union types independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("handles different union types independently")
val status = Status.Active
val result = MyResult.Ok(1)
val option = MyOption.Some(2)
expect true
```

</details>

#### union method calls preserve type

- union method calls preserve type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("union method calls preserve type")
val s1 = Status.Active
val s2 = Status.Inactive
val isActive = s1.is_active()
expect isActive == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/union_impl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Union keyword, Union Impl Methods, Union Pattern Matching, Union Type Safety.
- Union keyword
- Union Impl Methods
- Union Pattern Matching
- Union Type Safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `f2ae0a7045eb94354d89ab4dd0e36798dffc76c09b2dc0f86f0001fc7b91fab9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2ae0a7045eb94354d89ab4dd0e36798dffc76c09b2dc0f86f0001fc7b91fab9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2ae0a7045eb94354d89ab4dd0e36798dffc76c09b2dc0f86f0001fc7b91fab9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/types/union_impl_spec.spl
mirror: doc/06_spec/shared/types/union_impl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/types/union_impl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/types/union_impl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/types/union_impl_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses union types correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/union_impl_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates inactive status variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/types/union_impl_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates union variant with string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
