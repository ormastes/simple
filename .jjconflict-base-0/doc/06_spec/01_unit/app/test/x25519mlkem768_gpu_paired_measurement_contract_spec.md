# X25519mlkem768 Gpu Paired Measurement Contract Specification

> Tests covering X25519MLKEM768 GPU paired measurement prerequisite contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Paired Measurement Contract Specification

## Scenarios

### X25519MLKEM768 GPU paired measurement prerequisite contract

#### accepts only an even ABBA sample count in 30 through 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind ninety kernel events to thirty three-operation exchanges")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(90), 30, 90)).to_equal("")
expect(x25519_mlkem768_gpu_timed_lifecycle_reason(
    _delta(120), 30, 120)).to_equal("")
```

</details>

#### rejects exchange-count substitution and malformed lifecycle deltas

- var unequal =  delta


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_gpu_paired_measurement_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 GPU paired measurement prerequisite contract.
- X25519MLKEM768 GPU paired measurement prerequisite contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
