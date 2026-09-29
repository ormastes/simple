# 00 Preflight Specification

> Tests covering T32 hardware preflight.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 00 Preflight Specification

## Scenarios

### T32 hardware preflight

#### tool availability

#### detects T32 installation

- detects T32 installation
   - Expected: available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects T32 installation")
val available = t32_hw_t32rem_available()
expect(available).to_equal(true)
```

</details>

#### T32 RCL port is reachable

- T32 RCL port is reachable
   - Expected: reachable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("T32 RCL port is reachable")
val reachable = t32_hw_probe_available()
expect(reachable).to_equal(true)
```

</details>

#### version checks

#### queries T32 version

- queries T32 version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queries T32 version")
val version = t32_hw_query_version()
expect(version).to_be_greater_than(0)
```

</details>

#### version meets OLD tool minimum

- version meets OLD tool minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("version meets OLD tool minimum")
val version = t32_hw_query_version()
expect(version).to_be_greater_than(T32_HW_MIN_VERSION_OLD - 1)
```

</details>

#### relay infrastructure

#### relay scripts accessible

- relay scripts accessible
   - Expected: available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("relay scripts accessible")
val available = t32_hw_relay_available()
expect(available).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/00_preflight_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 hardware preflight.
- T32 hardware preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `936b80a0a9de3e0616ff529695a6df42393283797ed091140b36cdec9c5c3e6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `936b80a0a9de3e0616ff529695a6df42393283797ed091140b36cdec9c5c3e6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `936b80a0a9de3e0616ff529695a6df42393283797ed091140b36cdec9c5c3e6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/00_preflight_spec.spl
mirror: doc/06_spec/integration/t32_hw/00_preflight_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/00_preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/00_preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/00_preflight_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects T32 installation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/00_preflight_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 RCL port is reachable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/00_preflight_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'queries T32 version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
