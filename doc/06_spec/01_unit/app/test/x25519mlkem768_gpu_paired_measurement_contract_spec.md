# x25519mlkem768_gpu_paired_measurement_contract_spec

> Operator-facing admission contract for GPU paired timing runs. Audience:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_gpu_paired_measurement_contract_spec

Operator-facing admission contract for GPU paired timing runs. Audience:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Operator-facing admission contract for GPU paired timing runs. Audience:
    GPU acceleration-lane owners and performance engineers. Scope: the sample
    count and lifecycle-delta prerequisites a measurement must satisfy before
    its timing may be recorded — even ABBA sample counts in [30,1024], honest
    per-kernel lifecycle counts, and bounded aggregate/operation evidence.
    Assumptions: the frozen reason-string vocabulary below is the gate's
    public API.

## Scenarios

### X25519MLKEM768 GPU paired measurement prerequisite contract

#### accepts only an even ABBA sample count in 30 through 1024

- Check the paired sample-count bounds and evenness
   - Expected: x25519_mlkem768_gpu_paired_count_reason(30) equals ``
   - Expected: x25519_mlkem768_gpu_paired_count_reason(1024) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-PAIRED-MEASUREMENT
step("Check the paired sample-count bounds and evenness")
expect(x25519_mlkem768_gpu_paired_count_reason(30)).to_equal("")
expect(x25519_mlkem768_gpu_paired_count_reason(1024)).to_equal("")
expect(x25519_mlkem768_gpu_paired_count_reason(29)).to_equal(
    "gpu-paired-sample-count-too-small")
expect(x25519_mlkem768_gpu_paired_count_reason(1025)).to_equal(
    "gpu-paired-sample-count-too-large")
expect(x25519_mlkem768_gpu_paired_count_reason(31)).to_equal(
    "gpu-paired-sample-count-not-even")
```

</details>

#### admits honest multi-kernel lifecycle counts instead of exchange counts

- Bind ninety kernel events to thirty three-operation exchanges


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-PAIRED-MEASUREMENT
step("Bind ninety kernel events to thirty three-operation exchanges")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(90), 30, 90)).to_equal("")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(120), 30, 120)).to_equal("")
```

</details>

#### rejects exchange-count substitution and malformed lifecycle deltas

- Substitute exchange counts and break a lifecycle delta


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-PAIRED-MEASUREMENT
step("Substitute exchange counts and break a lifecycle delta")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(30), 30, 30)).to_equal(
    "gpu-timed-kernel-count-too-small")
var unequal = _delta(90)
unequal.readback_count = 89
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    unequal, 30, 90)).to_equal(
    "gpu-timed-lifecycle-delta-invalid")
```

</details>

#### rejects invalid aggregate bounds and operation evidence counts

- Push aggregate and operation counts out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-PAIRED-MEASUREMENT
step("Push aggregate and operation counts out of bounds")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(90), 29, 90)).to_equal(
    "gpu-timed-full-exchange-count-invalid")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(3072), 1025, 3072)).to_equal(
    "gpu-timed-full-exchange-count-invalid")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(93), 31, 93)).to_equal(
    "gpu-timed-full-exchange-count-invalid")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(90), 30, 0)).to_equal(
    "gpu-timed-operation-kernel-count-invalid")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(90), 30, 91)).to_equal(
    "gpu-timed-operation-kernel-count-mismatch")
```

</details>

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

- `REQ-X25519MLKEM768-PAIRED-MEASUREMENT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `920a290c8f92a7cc4dacf0c2f18803aefd41a5202349b13d7dbc6a0e263554a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `920a290c8f92a7cc4dacf0c2f18803aefd41a5202349b13d7dbc6a0e263554a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `920a290c8f92a7cc4dacf0c2f18803aefd41a5202349b13d7dbc6a0e263554a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: 01_unit/app/test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl
mirror: doc/06_spec/x25519mlkem768_gpu_paired_measurement_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/x25519mlkem768_gpu_paired_measurement_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/x25519mlkem768_gpu_paired_measurement_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only an even ABBA sample count in 30 through 1024' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits honest multi-kernel lifecycle counts instead of exchange counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects exchange-count substitution and malformed lifecycle deltas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
