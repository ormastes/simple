# Time Ops Unix Specification

> Tests covering app.io.time_ops, time_now_unix_micros, current_time_unix, current_time_ms, time ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Ops Unix Specification

## Scenarios

### app.io.time_ops

### time_now_unix_micros

#### returns positive value

- returns positive value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns positive value")
val t = time_now_unix_micros()
expect(t).to_be_greater_than(0)
```

</details>

### current_time_unix

#### returns seconds since epoch

- returns seconds since epoch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns seconds since epoch")
val t = current_time_unix()
expect(t).to_be_greater_than(1700000000)
```

</details>

### current_time_ms

#### returns milliseconds since epoch

- returns milliseconds since epoch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns milliseconds since epoch")
val t = current_time_ms()
expect(t).to_be_greater_than(1700000000000)
```

</details>

### time ordering

#### micros > ms > unix

- micros > ms > unix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("micros > ms > unix")
val micros = time_now_unix_micros()
val ms = current_time_ms()
val unix = current_time_unix()
expect(micros).to_be_greater_than(ms)
expect(ms).to_be_greater_than(unix)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/io/time_ops_unix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app.io.time_ops, time_now_unix_micros, current_time_unix, current_time_ms, time ordering.
- app.io.time_ops
- time_now_unix_micros
- current_time_unix
- current_time_ms
- time ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `5a261208637bcd146f51060817500acaf7987bd75bf99f2c99b6c46b4fc1b181`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a261208637bcd146f51060817500acaf7987bd75bf99f2c99b6c46b4fc1b181`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a261208637bcd146f51060817500acaf7987bd75bf99f2c99b6c46b4fc1b181`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/io/time_ops_unix_spec.spl
mirror: doc/06_spec/unit/app/io/time_ops_unix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/io/time_ops_unix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/io/time_ops_unix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/io/time_ops_unix_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns positive value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/io/time_ops_unix_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns seconds since epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/io/time_ops_unix_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns milliseconds since epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
