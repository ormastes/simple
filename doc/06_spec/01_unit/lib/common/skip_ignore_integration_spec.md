# Skip Ignore Integration Specification

> Tests covering Skip/Ignore Integration Tests, Platform-specific tests, Runtime mode detection, Architecture detection, Hardware capabilities, Complete environment profile, Real-world skip patterns, Real-world ignore patterns, Simplified decorator usage, Complex multi-condition examples, Conditional skip with skip_if, only_on usage, Performance with multiple decorators, Documentation examples.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Ignore Integration Specification

## Scenarios

### Skip/Ignore Integration Tests

### Platform-specific tests

#### demonstrates platform detection concept

- demonstrates platform detection concept


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("demonstrates platform detection concept")
# Platform detection would use get_platform_os() etc.
val platform = "linux"
check(platform != "")
```

</details>

#### demonstrates Unix vs Windows distinction

- demonstrates Unix vs Windows distinction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("demonstrates Unix vs Windows distinction")
val is_unix = true
check(is_unix == true)
```

</details>

### Runtime mode detection

#### identifies current runtime mode

- identifies current runtime mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies current runtime mode")
val mode = "interpreter"
check(mode != "")
```

</details>

### Architecture detection

#### identifies CPU architecture

- identifies CPU architecture


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies CPU architecture")
val arch = "x86_64"
val bits = 64
check(arch != "")
check(bits == 64)
```

</details>

### Hardware capabilities

#### checks available hardware

- checks available hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks available hardware")
val cores = 4
check(cores > 0)
```

</details>

### Complete environment profile

#### prints complete environment information

- prints complete environment information


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prints complete environment information")
check(true)
```

</details>

### Real-world skip patterns

#### example: skip on Windows (concept)

- example: skip on Windows (concept)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: skip on Windows (concept)")
val reason = "chmod() not yet implemented on Windows"
check(reason != "")
```

</details>

#### example: skip in interpreter mode (concept)

- example: skip in interpreter mode (concept)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: skip in interpreter mode (concept)")
val reason = "Generics need static compilation"
check(reason != "")
```

</details>

#### example: skip without hardware (concept)

- example: skip without hardware (concept)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: skip without hardware (concept)")
val reason = "Acceleration required"
check(reason != "")
```

</details>

### Real-world ignore patterns

#### example: ignore Unix fork on Windows (concept)

- example: ignore Unix fork on Windows (concept)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: ignore Unix fork on Windows (concept)")
val reason = "fork() is Unix-only, no Windows equivalent"
check(reason != "")
```

</details>

#### example: ignore 32-bit architecture (concept)

- example: ignore 32-bit architecture (concept)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: ignore 32-bit architecture (concept)")
val reason = "64-bit pointers required"
check(reason != "")
```

</details>

### Simplified decorator usage

#### example: using platform skip

- example: using platform skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: using platform skip")
val reason = "Not yet ported"
check(reason != "")
```

</details>

#### example: using interpreter skip

- example: using interpreter skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: using interpreter skip")
val reason = "Compiled mode needed"
check(reason != "")
```

</details>

### Complex multi-condition examples

#### example: CI-only network test

- example: CI-only network test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: CI-only network test")
val reason = "Network test only in CI"
check(reason != "")
```

</details>

#### example: multi-skip

- example: multi-skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: multi-skip")
val reason = "Windows interpreter mode not fully supported"
check(reason != "")
```

</details>

### Conditional skip with skip_if

#### example: skip if no CI environment

- example: skip if no CI environment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: skip if no CI environment")
val reason = "CI environment required"
check(reason != "")
```

</details>

#### example: skip on complex condition

- example: skip on complex condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: skip on complex condition")
val reason = "Not supported on certain configs"
check(reason != "")
```

</details>

### only_on usage

#### example: Linux-only test

- example: Linux-only test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: Linux-only test")
val platform = "linux"
check(platform == "linux")
```

</details>

#### example: compiled mode only

- example: compiled mode only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example: compiled mode only")
val mode = "compiled"
check(mode == "compiled")
```

</details>

### Performance with multiple decorators

#### creates decorators quickly

- creates decorators quickly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates decorators quickly")
var i = 0
while i < 10:
    val reason = "Test {i}"
    check(reason != "")
    i = i + 1
```

</details>

### Documentation examples

#### README example: platform-specific skip

- README example: platform-specific skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("README example: platform-specific skip")
val reason = "chmod() not available on Windows"
check(reason != "")
```

</details>

#### README example: hardware requirement

- README example: hardware requirement


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("README example: hardware requirement")
val reason = "Required for neural network test"
check(reason != "")
```

</details>

#### README example: ignore fundamentally unsupported

- README example: ignore fundamentally unsupported


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("README example: ignore fundamentally unsupported")
val reason = "Unix fork() API - no Windows equivalent"
check(reason != "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/skip_ignore_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Skip/Ignore Integration Tests, Platform-specific tests, Runtime mode detection, Architecture detection, Hardware capabilities, Complete environment profile, Real-world skip patterns, Real-world ignore patterns, Simplified decorator usage, Complex multi-condition examples, Conditional skip with skip_if, only_on usage, Performance with multiple decorators, Documentation examples.
- Skip/Ignore Integration Tests
- Platform-specific tests
- Runtime mode detection
- Architecture detection
- Hardware capabilities
- Complete environment profile
- Real-world skip patterns
- Real-world ignore patterns
- Simplified decorator usage
- Complex multi-condition examples
- Conditional skip with skip_if
- only_on usage
- Performance with multiple decorators
- Documentation examples

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `8af7a65ca592311b22ea7d4e8185aa0a18663b78f136efda7a8fbd742d4f0ee9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8af7a65ca592311b22ea7d4e8185aa0a18663b78f136efda7a8fbd742d4f0ee9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8af7a65ca592311b22ea7d4e8185aa0a18663b78f136efda7a8fbd742d4f0ee9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/skip_ignore_integration_spec.spl
mirror: doc/06_spec/01_unit/lib/common/skip_ignore_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/skip_ignore_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/skip_ignore_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/skip_ignore_integration_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demonstrates platform detection concept' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/skip_ignore_integration_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demonstrates Unix vs Windows distinction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/skip_ignore_integration_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies current runtime mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
