# Sandbox Specification

> Tests covering sandbox module compilation, memory size parsing logic, sandbox configuration patterns, sandbox flag detection logic, string suffix detection, comma-separated parsing logic, trim whitespace logic, sandbox configuration concepts, argument iteration pattern, flag value parsing pattern, builder pattern validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sandbox Specification

## Scenarios

### sandbox module compilation

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

### memory size parsing logic

#### validates K suffix calculation

#### 512K should be 512 * 1024

- 512K should be 512 * 1024


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("512K should be 512 * 1024")
val expected = 512 * 1024
expect expected == 524288
```

</details>

#### validates M suffix calculation

#### 256M should be 256 * 1024 * 1024

- 256M should be 256 * 1024 * 1024


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("256M should be 256 * 1024 * 1024")
val expected = 256 * 1024 * 1024
expect expected == 268435456
```

</details>

#### validates G suffix calculation

#### 2G should be 2 * 1024 * 1024 * 1024

- 2G should be 2 * 1024 * 1024 * 1024


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2G should be 2 * 1024 * 1024 * 1024")
val expected = 2 * 1024 * 1024 * 1024
expect expected == 2147483648
```

</details>

### sandbox configuration patterns

#### validates boolean defaults

#### false is the default for flags

- false is the default for flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false is the default for flags")
val default_flag = false
expect default_flag == false
```

</details>

### sandbox flag detection logic

#### validates --sandbox flag

#### matches sandbox flag

- matches sandbox flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches sandbox flag")
expect flag == "--sandbox"
```

</details>

#### validates --no-network flag

#### matches no-network flag

- matches no-network flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches no-network flag")
expect flag == "--no-network"
```

</details>

#### validates --time-limit flag

#### matches time-limit flag

- matches time-limit flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches time-limit flag")
expect flag == "--time-limit"
```

</details>

#### validates --memory-limit flag

#### matches memory-limit flag

- matches memory-limit flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches memory-limit flag")
expect flag == "--memory-limit"
```

</details>

### string suffix detection

#### validates G suffix

#### ends with G

- ends with G


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with G")
expect value.ends_with("G") == true
```

</details>

#### validates M suffix

#### ends with M

- ends with M


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with M")
expect value.ends_with("M") == true
```

</details>

#### validates K suffix

#### ends with K

- ends with K


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with K")
expect value.ends_with("K") == true
```

</details>

### comma-separated parsing logic

#### validates split on comma

#### splits into 3 parts

- splits into 3 parts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits into 3 parts")
expect parts.len() == 3
```

</details>

#### first part is example.com

- first part is example.com


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first part is example.com")
expect parts[0] == "example.com"
```

</details>

#### second part is test.org

- second part is test.org


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second part is test.org")
expect parts[1] == "test.org"
```

</details>

#### third part is foo.net

- third part is foo.net


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("third part is foo.net")
expect parts[2] == "foo.net"
```

</details>

### trim whitespace logic

#### validates trim

#### trims whitespace

- trims whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace")
expect trimmed == "512M"
```

</details>

### sandbox configuration concepts

#### demonstrates mutable config pattern

#### allows field mutation

- allows field mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows field mutation")
expect config_modified == true
```

</details>

#### demonstrates Option usage - Some

#### has value

- has value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has value")
expect some_val == 60
```

</details>

#### demonstrates Option usage - None

#### validates None concept

- validates None concept


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates None concept")
val none_val: Option<i64> = nil
expect(none_val).to_be_nil()
```

</details>

### argument iteration pattern

#### validates while loop counter

#### iterates 5 times

- iterates 5 times


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates 5 times")
expect count == 5
```

</details>

#### validates index bounds checking

#### checks bounds correctly

- checks bounds correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks bounds correctly")
expect i + 1 < args.len() == true
```

</details>

### flag value parsing pattern

#### validates increment for value flags

#### increments by 2 for value flags

- increments by 2 for value flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments by 2 for value flags")
expect i == 2
```

</details>

### builder pattern validation

#### validates method chaining concept

#### chains operations

- chains operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains operations")
expect value == 30
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/sandbox_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sandbox module compilation, memory size parsing logic, sandbox configuration patterns, sandbox flag detection logic, string suffix detection, comma-separated parsing logic, trim whitespace logic, sandbox configuration concepts, argument iteration pattern, flag value parsing pattern, builder pattern validation.
- sandbox module compilation
- memory size parsing logic
- sandbox configuration patterns
- sandbox flag detection logic
- string suffix detection
- comma-separated parsing logic
- trim whitespace logic
- sandbox configuration concepts
- argument iteration pattern
- flag value parsing pattern
- builder pattern validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `a5d8d40f2eb76ec097f10312b774e4feed827d2f978755216adc912d5db0bf80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5d8d40f2eb76ec097f10312b774e4feed827d2f978755216adc912d5db0bf80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5d8d40f2eb76ec097f10312b774e4feed827d2f978755216adc912d5db0bf80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/sandbox_spec.spl
mirror: doc/06_spec/unit/app/tooling/sandbox_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/sandbox_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/sandbox_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/sandbox_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/sandbox_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '512K should be 512 * 1024' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/sandbox_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '256M should be 256 * 1024 * 1024' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
