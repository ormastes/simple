# Coverage Specification

> Tests covering coverage module compilation, coverage enabled check, early return when disabled, quiet mode, Result handling, match on Result with early return, Option handling for coverage, match on Option, coverage stats struct, string interpolation, early return pattern, nested early returns, boolean negation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Specification

## Scenarios

### coverage module compilation

#### compiles successfully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles successfully")
expect 1 + 1 == 2
```

</details>

### coverage enabled check

#### returns false when disabled

- returns false when disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when disabled")
val enabled = false
expect enabled == false
```

</details>

#### returns true when enabled

- returns true when enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when enabled")
val enabled = true
expect enabled == true
```

</details>

### early return when disabled

#### should return early if not enabled

- should return early if not enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return early if not enabled")
val enabled = false
val should_return = not enabled
expect should_return == true
```

</details>

#### should continue if enabled

- should continue if enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should continue if enabled")
val enabled = true
val should_return = not enabled
expect should_return == false
```

</details>

### quiet mode

#### quiet true suppresses output

- quiet true suppresses output


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quiet true suppresses output")
val quiet = true
expect quiet == true
```

</details>

#### quiet false allows output

- quiet false allows output


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quiet false allows output")
val quiet = false
expect quiet == false
```

</details>

### Result handling

#### Ok result check

- Ok result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok result check")
expect Ok("saved").is_ok() == true
```

</details>

#### Err result check

- Err result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Err result check")
expect Err("failed").is_err() == true
```

</details>

### match on Result with early return

#### matches Err and returns

- matches Err and returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Err and returns")
val result = Err("failed")
val matched = match result:
    Err(e) => "error"
    Ok(_) => "success"
expect matched == "error"
```

</details>

#### matches Ok and continues

- matches Ok and continues


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Ok and continues")
val result = Ok("saved")
val matched = match result:
    Err(e) => "error"
    Ok(_) => "success"
expect matched == "success"
```

</details>

### Option handling for coverage

#### Some contains coverage data

- Some contains coverage data


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some contains coverage data")
val cov = Some("data")
expect cov.is_some() == true
```

</details>

#### unwrap gets coverage data

- unwrap gets coverage data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap gets coverage data")
val cov = Some("data")
val data = cov.unwrap()
expect data == "data"
```

</details>

### match on Option

#### matches Some

- matches Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Some")
val cov = Some("data")
val matched = match cov:
    Some(c) => "has_coverage"
    None => "no_coverage"
expect matched == "has_coverage"
```

</details>

#### checks is_some and is_none

- checks is_some and is_none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks is_some and is_none")
val has_cov = Some("data")
expect has_cov.is_some() == true
```

</details>

### coverage stats struct

#### constructs with all fields

- constructs with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with all fields")
val total_lines = 100
val total_files = 5
val total_functions = 20
val total_ffi_calls = 10
expect total_lines == 100
expect total_files == 5
```

</details>

### string interpolation

#### interpolates path

- interpolates path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates path")
val path = "build/coverage/coverage.json"
val msg = "Coverage data saved to: {path}"
expect msg.contains(".coverage") == true
```

</details>

#### interpolates stats

- interpolates stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates stats")
val lines = 100
val msg = "  Lines executed: {lines}"
expect msg.contains("100") == true
```

</details>

### early return pattern

#### returns early when condition true

- returns early when condition true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns early when condition true")
val quiet = true
val should_return = quiet
expect should_return == true
```

</details>

#### continues when condition false

- continues when condition false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues when condition false")
val quiet = false
val should_return = quiet
expect should_return == false
```

</details>

### nested early returns

#### first check - not enabled

- first check - not enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first check - not enabled")
val enabled = false
val should_return_1 = not enabled
expect should_return_1 == true
```

</details>

#### second check - save failed and quiet

- second check - save failed and quiet


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second check - save failed and quiet")
val save_ok = false
val quiet = true
val should_return_2 = not save_ok and quiet
expect should_return_2 == true
```

</details>

#### third check - quiet mode

- third check - quiet mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("third check - quiet mode")
val quiet = true
val should_return_3 = quiet
expect should_return_3 == true
```

</details>

### boolean negation

#### not true equals false

- not true equals false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not true equals false")
expect not true == false
```

</details>

#### not false equals true

- not false equals true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not false equals true")
expect not false == true
```

</details>

#### double negation

- double negation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("double negation")
val enabled = true
expect not (not enabled) == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering coverage module compilation, coverage enabled check, early return when disabled, quiet mode, Result handling, match on Result with early return, Option handling for coverage, match on Option, coverage stats struct, string interpolation, early return pattern, nested early returns, boolean negation.
- coverage module compilation
- coverage enabled check
- early return when disabled
- quiet mode
- Result handling
- match on Result with early return
- Option handling for coverage
- match on Option
- coverage stats struct
- string interpolation
- early return pattern
- nested early returns
- boolean negation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `085e48404f38e1b048915d48639d14240ed7ca8f5d96966ae75433e02119c472`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `085e48404f38e1b048915d48639d14240ed7ca8f5d96966ae75433e02119c472`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `085e48404f38e1b048915d48639d14240ed7ca8f5d96966ae75433e02119c472`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/app/tooling/coverage_spec.spl
mirror: doc/06_spec/unit/app/tooling/coverage_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/coverage_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/coverage_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false when disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/coverage_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true when enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/coverage_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return early if not enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/coverage_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should continue if enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
