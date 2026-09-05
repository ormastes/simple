# X25519mlkem768 Gpu Paired Measurement Specification

> Tests covering X25519MLKEM768 fail-closed GPU paired collector preflight.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Paired Measurement Specification

## Scenarios

### X25519MLKEM768 fail-closed GPU paired collector preflight

#### rejects invalid ABBA counts before any qualification claim

- qualification,  config
-  admission for
-  lifecycle
   - Expected: result.reason equals `gpu-paired-sample-count-not-even`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val result = x25519_mlkem768_collect_gpu_paired_measurement(
    qualification, _config(qualification),
    _admission_for(qualification), _evidence(qualification),
    _lifecycle(), 31)
expect(result.collected).to_be(false)
expect(result.blocker).to_equal(
    X25519MlKem768GpuPairedMeasurementBlocker.InvalidPairCount)
expect(result.reason).to_equal("gpu-paired-sample-count-not-even")
```

</details>

#### keeps generic CUDA and Vulkan diagnostics blocked from collection

- Caller-constructible evidence is never trusted as live proof
- qualification,  config
-  admission for
-  evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Caller-constructible evidence is never trusted as live proof")
for backend in [X25519MlKem768EvidenceBackend.Cuda,
        X25519MlKem768EvidenceBackend.Vulkan]:
    val qualification = _qualification(backend)
    val result = x25519_mlkem768_collect_gpu_paired_measurement(
        qualification, _config(qualification),
        _admission_for(qualification),
        _evidence(qualification), _lifecycle(), 30)
    expect(result.collected).to_be(false)
    expect(result.blocker).to_equal(
        X25519MlKem768GpuPairedMeasurementBlocker.TrustedLiveExecutorAdmissionUnavailable)
    expect(result.reason).to_equal(
        "gpu-paired-trusted-live-executor-admission-unavailable")
```

</details>

#### preserves the pinned Metal qualification blocker

- qualification,  config
-  admission for
-  evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _qualification(X25519MlKem768EvidenceBackend.Metal)
val result = x25519_mlkem768_collect_gpu_paired_measurement(
    qualification, _config(qualification),
    _admission_for(qualification),
    _evidence(qualification), _lifecycle(), 30)
expect(result.collected).to_be(false)
expect(result.blocker).to_equal(
    X25519MlKem768GpuPairedMeasurementBlocker.QualificationRejected)
expect(result.reason).to_equal(
    "gpu-build-metal-metallib-and-live-identity-not-pinned")
```

</details>

#### preserves the canonical qualification rejection reason

- var evidence =  evidence
- qualification,  config
-  admission for
-  lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _qualification(
    X25519MlKem768EvidenceBackend.Cuda)
var evidence = _evidence(qualification)
evidence.fallback_used = true
val result = x25519_mlkem768_collect_gpu_paired_measurement(
    qualification, _config(qualification),
    _admission_for(qualification), evidence,
    _lifecycle(), 30)
expect(result.collected).to_be(false)
expect(result.blocker).to_equal(
    X25519MlKem768GpuPairedMeasurementBlocker.QualificationRejected)
expect(result.reason).to_equal(
    "gpu-measurement-fallback-or-oracle-mismatch")
```

</details>

#### contains no timing crypto RSS or synthetic-lifecycle success path

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read_text(
    "src/app/test/x25519mlkem768_gpu_paired_measurement.spl")
expect(source).to_contain(
    "x25519_mlkem768_qualified_gpu_measurement_reason")
expect(source).to_contain(
    "TrustedLiveExecutorAdmissionUnavailable")
expect(source.contains("time_now_nanos")).to_be(false)
expect(source.contains("platform_measurement_refresh_process_rss")).to_be(false)
expect(source.contains("x25519_mlkem768_keygen")).to_be(false)
expect(source.contains("lifecycle_snapshot()")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_gpu_paired_measurement_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 fail-closed GPU paired collector preflight.
- X25519MLKEM768 fail-closed GPU paired collector preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
