# Config Ffi Specification

> Tests covering Runtime Configuration FFI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Ffi Specification

## Scenarios

### Runtime Configuration FFI

#### should enable and disable macro trace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should enable and disable macro trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should enable and disable macro trace")
# Default should be false
check(not rt_is_macro_trace_enabled())

# Enable it
rt_set_macro_trace(true)
check(rt_is_macro_trace_enabled())

# Disable it
rt_set_macro_trace(false)
check(not rt_is_macro_trace_enabled())
```

</details>

#### should enable and disable debug mode

- should enable and disable debug mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should enable and disable debug mode")
# Default should be false
check(not rt_is_debug_mode_enabled())

# Enable it
rt_set_debug_mode(true)
check(rt_is_debug_mode_enabled())

# Disable it
rt_set_debug_mode(false)
check(not rt_is_debug_mode_enabled())
```

</details>

#### should maintain independent flags

- should maintain independent flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should maintain independent flags")
# Set macro trace on, debug mode off
rt_set_macro_trace(true)
rt_set_debug_mode(false)

check(rt_is_macro_trace_enabled())
check(not rt_is_debug_mode_enabled())

# Swap them
rt_set_macro_trace(false)
rt_set_debug_mode(true)

check(not rt_is_macro_trace_enabled())
check(rt_is_debug_mode_enabled())

# Clean up
rt_set_debug_mode(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/config_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Runtime Configuration FFI.
- Runtime Configuration FFI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `ab91b927852fc0fd1849d473c6451b636fbe89377a662944cc52439513bcbc98`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab91b927852fc0fd1849d473c6451b636fbe89377a662944cc52439513bcbc98`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab91b927852fc0fd1849d473c6451b636fbe89377a662944cc52439513bcbc98`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/tooling/config_ffi_spec.spl
mirror: doc/06_spec/unit/app/tooling/config_ffi_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/config_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/config_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/config_ffi_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enable and disable macro trace' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/config_ffi_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should enable and disable macro trace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/config_ffi_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enable and disable debug mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/config_ffi_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should enable and disable debug mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/config_ffi_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should maintain independent flags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/config_ffi_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should maintain independent flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
