# Timing Separation Specification

> Tests covering TestFileResult setup_ms, TestRunResult total_setup_ms.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timing Separation Specification

## Scenarios

### TestFileResult setup_ms

#### has setup_ms field defaulting to 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has setup_ms field defaulting to 0
   - Expected: test_setup_ms_default() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has setup_ms field defaulting to 0")
expect(test_setup_ms_default()).to_equal(true)
```

</details>

#### can hold non-zero setup_ms

- can hold non-zero setup_ms
   - Expected: test_setup_ms_nonzero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can hold non-zero setup_ms")
expect(test_setup_ms_nonzero()).to_equal(true)
```

</details>

#### setup_ms is independent of duration_ms

- setup_ms is independent of duration_ms
   - Expected: test_setup_ms_independent() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("setup_ms is independent of duration_ms")
expect(test_setup_ms_independent()).to_equal(true)
```

</details>

### TestRunResult total_setup_ms

#### has total_setup_ms field

- has total_setup_ms field
   - Expected: test_run_result_setup_ms() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has total_setup_ms field")
expect(test_run_result_setup_ms()).to_equal(true)
```

</details>

#### defaults to 0

- defaults to 0
   - Expected: test_run_result_setup_ms_zero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to 0")
expect(test_run_result_setup_ms_zero()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner/timing_separation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestFileResult setup_ms, TestRunResult total_setup_ms.
- TestFileResult setup_ms
- TestRunResult total_setup_ms

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f93a77220861a214a605d0ee043bfeb1a00e183c689b27045ffb93488d901fed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f93a77220861a214a605d0ee043bfeb1a00e183c689b27045ffb93488d901fed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f93a77220861a214a605d0ee043bfeb1a00e183c689b27045ffb93488d901fed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/app/test_runner/timing_separation_spec.spl
mirror: doc/06_spec/unit/app/test_runner/timing_separation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner/timing_separation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner/timing_separation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner/timing_separation_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has setup_ms field defaulting to 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner/timing_separation_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can hold non-zero setup_ms' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner/timing_separation_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can hold non-zero setup_ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner/timing_separation_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'setup_ms is independent of duration_ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
