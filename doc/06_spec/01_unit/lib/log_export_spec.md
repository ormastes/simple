# Log Export Specification

> Tests covering Log module exports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Export Specification

## Scenarios

### Log module exports

#### LOG_ERROR constant is accessible

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- LOG_ERROR constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_ERROR constant is accessible")
check(LOG_ERROR == 2)
```

</details>

#### LOG_WARN constant is accessible

- LOG_WARN constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_WARN constant is accessible")
check(LOG_WARN == 3)
```

</details>

#### LOG_INFO constant is accessible

- LOG_INFO constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_INFO constant is accessible")
check(LOG_INFO == 4)
```

</details>

#### LOG_DEBUG constant is accessible

- LOG_DEBUG constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_DEBUG constant is accessible")
check(LOG_DEBUG == 5)
```

</details>

#### LOG_TRACE constant is accessible

- LOG_TRACE constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_TRACE constant is accessible")
check(LOG_TRACE == 6)
```

</details>

#### LOG_FATAL constant is accessible

- LOG_FATAL constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_FATAL constant is accessible")
check(LOG_FATAL == 1)
```

</details>

#### LOG_OFF constant is accessible

- LOG_OFF constant is accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG_OFF constant is accessible")
check(LOG_OFF == 0)
```

</details>

#### error function is callable without crash

- error function is callable without crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error function is callable without crash")
check(true)
```

</details>

#### warn function is callable without crash

- warn function is callable without crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warn function is callable without crash")
check(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/log_export_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Log module exports.
- Log module exports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `db7a2ce9cb7d9e5fec56b14edc31c311dd48fcee9f77a07efdd59ff93e2c8ee4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db7a2ce9cb7d9e5fec56b14edc31c311dd48fcee9f77a07efdd59ff93e2c8ee4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db7a2ce9cb7d9e5fec56b14edc31c311dd48fcee9f77a07efdd59ff93e2c8ee4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/log_export_spec.spl
mirror: doc/06_spec/01_unit/lib/log_export_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/log_export_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/log_export_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/log_export_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LOG_ERROR constant is accessible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/log_export_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LOG_WARN constant is accessible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/log_export_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LOG_INFO constant is accessible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
