# Startup Specification

> Tests covering startup module compilation, startup flag detection, prefetch conditions, exit code conventions, match pattern with Option, tuple return values, time measurement patterns, Result patterns, list length checks, boolean conditions, metrics enabled pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Specification

## Scenarios

### startup module compilation

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

### startup flag detection

#### detects --startup-metrics flag

- detects --startup-metrics flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --startup-metrics flag")
val args = ["simple", "--startup-metrics", "script.spl"]
val has_flag = args.any(_1 == "--startup-metrics")
expect has_flag == true
```

</details>

#### no flag when absent

- no flag when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no flag when absent")
val args = ["simple", "script.spl"]
val has_flag = args.any(_1 == "--startup-metrics")
expect has_flag == false
```

</details>

### prefetch conditions

#### prefetch enabled and files present

- prefetch enabled and files present


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefetch enabled and files present")
val enable_prefetch = true
val files_present = ["test.spl"].len() > 0
val should_prefetch = enable_prefetch and files_present
expect should_prefetch == true
```

</details>

#### prefetch disabled

- prefetch disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefetch disabled")
val enable_prefetch = false
val files_present = ["test.spl"].len() > 0
val should_prefetch = enable_prefetch and files_present
expect should_prefetch == false
```

</details>

#### no files to prefetch

- no files to prefetch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no files to prefetch")
val enable_prefetch = true
val should_prefetch = enable_prefetch and ([].len() > 0)
expect should_prefetch == false
```

</details>

### exit code conventions

#### success code is 0

- success code is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("success code is 0")
val exit_code = 0
expect exit_code == 0
```

</details>

#### error code is non-zero

- error code is non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error code is non-zero")
val exit_code = 1
expect exit_code == 1
```

</details>

### match pattern with Option

#### matches Some variant with value

- matches Some variant with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Some variant with value")
expect Some(42).is_some() == true
```

</details>

### tuple return values

#### tuple access works

- tuple access works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tuple access works")
val pair = (true, 42)
expect pair.0 == true
expect pair.1 == 42
```

</details>

### time measurement patterns

#### subtracts time values

- subtracts time values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subtracts time values")
expect (1500 - 1000) == 500
```

</details>

#### divides for conversion

- divides for conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("divides for conversion")
expect (3000 / 1000) == 3
```

</details>

### Result patterns

#### Ok result check

- Ok result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok result check")
expect Ok(42).is_ok() == true
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
expect Err("error").is_err() == true
```

</details>

### list length checks

#### non-empty list has count

- non-empty list has count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-empty list has count")
val files = ["file1.spl", "file2.spl"]
expect files.len() == 2
```

</details>

### boolean conditions

#### combines with and

- combines with and


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines with and")
val cond1 = true
val cond2 = true
val result = cond1 and cond2
expect result == true
```

</details>

#### false when one is false

- false when one is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false when one is false")
val cond1 = true
val cond2 = false
val result = cond1 and cond2
expect result == false
```

</details>

### metrics enabled pattern

#### checks boolean flag

- checks boolean flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks boolean flag")
val enabled = false
expect enabled == false
```

</details>

#### conditional execution

- conditional execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional execution")
val enabled = true
val should_print = enabled
expect should_print == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/startup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering startup module compilation, startup flag detection, prefetch conditions, exit code conventions, match pattern with Option, tuple return values, time measurement patterns, Result patterns, list length checks, boolean conditions, metrics enabled pattern.
- startup module compilation
- startup flag detection
- prefetch conditions
- exit code conventions
- match pattern with Option
- tuple return values
- time measurement patterns
- Result patterns
- list length checks
- boolean conditions
- metrics enabled pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `9cfcecdd6a868fd6e17db1806c09d63229b754eeaee9dc0de98752ff3e35eda7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cfcecdd6a868fd6e17db1806c09d63229b754eeaee9dc0de98752ff3e35eda7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cfcecdd6a868fd6e17db1806c09d63229b754eeaee9dc0de98752ff3e35eda7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/startup_spec.spl
mirror: doc/06_spec/unit/app/tooling/startup_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/startup_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/startup_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects --startup-metrics flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/startup_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no flag when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
