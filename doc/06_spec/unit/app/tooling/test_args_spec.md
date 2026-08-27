# Test Args Specification

> Tests covering test level flag patterns, boolean flag patterns, doctest flags, diagram flags, value flags, mutable struct pattern, option pattern, path detection, iteration pattern, bounds checking, default values, multiple flag sets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Args Specification

## Scenarios

### test level flag patterns

#### validates --unit flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates --unit flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --unit flag")
expect "--unit" == "--unit"
```

</details>

#### validates --integration flag

- validates --integration flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --integration flag")
expect "--integration" == "--integration"
```

</details>

#### validates --system flag

- validates --system flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --system flag")
expect "--system" == "--system"
```

</details>

### boolean flag patterns

#### validates --fail-fast

- validates --fail-fast


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --fail-fast")
expect "--fail-fast" == "--fail-fast"
```

</details>

#### validates --gc-log

- validates --gc-log


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --gc-log")
expect "--gc-log" == "--gc-log"
```

</details>

#### validates --watch

- validates --watch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --watch")
expect "--watch" == "--watch"
```

</details>

#### validates --json

- validates --json


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --json")
expect "--json" == "--json"
```

</details>

#### validates --doc

- validates --doc


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --doc")
expect "--doc" == "--doc"
```

</details>

### doctest flags

#### validates --doctest

- validates --doctest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --doctest")
expect "--doctest" == "--doctest"
```

</details>

#### validates --all

- validates --all


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --all")
expect "--all" == "--all"
```

</details>

#### validates --doctest-src

- validates --doctest-src


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --doctest-src")
expect "--doctest-src" == "--doctest-src"
```

</details>

#### validates --doctest-doc

- validates --doctest-doc


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --doctest-doc")
expect "--doctest-doc" == "--doctest-doc"
```

</details>

### diagram flags

#### validates --seq-diagram

- validates --seq-diagram


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --seq-diagram")
expect "--seq-diagram" == "--seq-diagram"
```

</details>

#### validates --diagram-all

- validates --diagram-all


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --diagram-all")
expect "--diagram-all" == "--diagram-all"
```

</details>

### value flags

#### validates --tag

- validates --tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --tag")
expect "--tag" == "--tag"
```

</details>

#### validates --seed

- validates --seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --seed")
expect "--seed" == "--seed"
```

</details>

#### validates --format

- validates --format


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates --format")
expect "--format" == "--format"
```

</details>

### mutable struct pattern

#### validates mutation

- validates mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates mutation")
var value = false
value = true
expect value == true
```

</details>

### option pattern

#### validates value assignment

- validates value assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates value assignment")
val value = "test.spl"
expect value == "test.spl"
```

</details>

### path detection

#### detects non-flag

- detects non-flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects non-flag")
val arg = "test.spl"
expect not arg.starts_with("-") == true
```

</details>

#### detects flag

- detects flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects flag")
val arg = "--flag"
expect arg.starts_with("-") == true
```

</details>

### iteration pattern

#### increments by 1

- increments by 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments by 1")
var i = 0
i = i + 1
expect i == 1
```

</details>

#### increments by 2

- increments by 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments by 2")
var i = 0
i = i + 2
expect i == 2
```

</details>

### bounds checking

#### validates index bounds

- validates index bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates index bounds")
val args = ["--flag", "value", "arg"]
val i = 0
expect i + 1 < args.len() == true
```

</details>

### default values

#### defaults to false

- defaults to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to false")
val default_val = false
expect default_val == false
```

</details>

### multiple flag sets

#### sets multiple flags

- sets multiple flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets multiple flags")
var flag1 = false
var flag2 = false
var flag3 = false
flag1 = true
flag2 = true
flag3 = true
expect flag1 == true
expect flag2 == true
expect flag3 == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/test_args_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test level flag patterns, boolean flag patterns, doctest flags, diagram flags, value flags, mutable struct pattern, option pattern, path detection, iteration pattern, bounds checking, default values, multiple flag sets.
- test level flag patterns
- boolean flag patterns
- doctest flags
- diagram flags
- value flags
- mutable struct pattern
- option pattern
- path detection
- iteration pattern
- bounds checking
- default values
- multiple flag sets

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

- Canonical SPipe generation for source `2b5532dca84978740176dba3080379b5eb9d81319eca72ff0761d77e63506b25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b5532dca84978740176dba3080379b5eb9d81319eca72ff0761d77e63506b25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b5532dca84978740176dba3080379b5eb9d81319eca72ff0761d77e63506b25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/test_args_spec.spl
mirror: doc/06_spec/unit/app/tooling/test_args_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/test_args_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/test_args_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/test_args_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates --unit flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_args_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates --integration flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_args_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates --system flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
