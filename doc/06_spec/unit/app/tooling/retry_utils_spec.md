# Retry Utils Specification

> Tests covering RetryUtils.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Retry Utils Specification

## Scenarios

### RetryUtils

#### computes exponential delay

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes exponential delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes exponential delay")
expect _retry_delay_ms(0, 25, 1000) == 25
expect _retry_delay_ms(3, 25, 1000) == 200
```

</details>

#### caps exponential delay

- caps exponential delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caps exponential delay")
expect _retry_delay_ms(8, 25, 500) == 500
```

</details>

#### retries transient statuses

- retries transient statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retries transient statuses")
expect _should_retry(1, 3, "timeout") == true
expect _should_retry(1, 3, "temporary") == true
```

</details>

#### stops on permanent status or exhausted attempts

- stops on permanent status or exhausted attempts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops on permanent status or exhausted attempts")
expect _should_retry(1, 3, "permanent") == false
expect _should_retry(3, 3, "timeout") == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/retry_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RetryUtils.
- RetryUtils

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

- Canonical SPipe generation for source `4344d1694ea3494053dfbcd8dfd214afcb6369cf0fd67b53ef5ea58aad79ba75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4344d1694ea3494053dfbcd8dfd214afcb6369cf0fd67b53ef5ea58aad79ba75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4344d1694ea3494053dfbcd8dfd214afcb6369cf0fd67b53ef5ea58aad79ba75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/retry_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/retry_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/retry_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/retry_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/retry_utils_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes exponential delay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/retry_utils_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caps exponential delay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/retry_utils_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retries transient statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
