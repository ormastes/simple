# X25519mlkem768 Performance Attestation Specification

> Tests covering X25519MLKEM768 qualified performance attestation v5.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Performance Attestation Specification

## Scenarios

### X25519MLKEM768 qualified performance attestation v5

#### admits qualified SIMD and GPU at their exact NFR thresholds

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simd_qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Avx2)
val simd_pair = perf_pair(simd_qualification, 122000, 72000)
val simd_receipt = admit_pair(simd_qualification, simd_pair)
expect(simd_receipt.status).to_equal(
    X25519MlKem768EvidenceStatus.Pass)
expect(simd_receipt.speedup_milli).to_equal(1500)
expect(simd_receipt.scalar_sample_set_sha256).to_equal(
    simd_pair.scalar_timed.sample_set_sha256)
val gpu_qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Cuda)
val gpu_pair = perf_pair(gpu_qualification, 97000, 72000)
val gpu_receipt = admit_pair(gpu_qualification, gpu_pair)
expect(gpu_receipt.status).to_equal(
    X25519MlKem768EvidenceStatus.Pass)
expect(gpu_receipt.speedup_milli).to_equal(1250)
```

</details>

#### rejects synthetic aggregates without the matching qualification

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avx = x25519_mlkem768_synthetic_measurement_qualification(
    X25519MlKem768EvidenceBackend.Avx2)
val neon = x25519_mlkem768_synthetic_measurement_qualification(
    X25519MlKem768EvidenceBackend.Neon)
val pair = perf_pair(avx, 122000, 72000)
val receipt = admit_pair(neon, pair)
expect(receipt.status).to_equal(
    X25519MlKem768EvidenceStatus.Blocked)
expect(receipt.reason).to_equal("measurement-qualification-mismatch")
```

</details>

<details>
<summary>Advanced: rejects a stale matrix row-set or source receipt binding</summary>

#### rejects a stale matrix row-set or source receipt binding

- var pair = perf pair
   - Expected: receipt.reason equals `measurement-qualification-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Rvv)
var pair = perf_pair(qualification, 122000, 72000)
pair.candidate.matrix_row_set_sha256 = "7" * 64
val receipt = admit_pair(qualification, pair)
expect(receipt.reason).to_equal("measurement-qualification-mismatch")
```

</details>


</details>

#### rejects a full-operation speedup below the backend threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Avx2)
val pair = perf_pair(qualification, 121000, 72000)
val receipt = admit_pair(qualification, pair)
expect(receipt.speedup_milli).to_equal(1490)
expect(receipt.reason).to_equal(
    "full-operation-speedup-below-threshold")
```

</details>

#### rejects stale toolchain identity and insufficient samples

- var stale = perf pair
- var wrong aggregate = perf pair
- var wrong scalar config = perf pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Neon)
var stale = perf_pair(qualification, 122000, 72000)
stale.candidate.crypto_source_sha256 = "8" * 64
expect(admit_pair(qualification, stale).reason).to_equal(
    "shared-workload-or-toolchain-identity-mismatch")
var wrong_aggregate = perf_pair(qualification, 122000, 72000)
wrong_aggregate.candidate.metrics.sample_count = 29
expect(admit_pair(qualification, wrong_aggregate).reason).to_equal(
    "invalid-native-full-operation-measurement")
var wrong_scalar_config = perf_pair(qualification, 122000, 72000)
wrong_scalar_config.scalar.backend_configuration_sha256 = "8" * 64
expect(admit_pair(qualification, wrong_scalar_config).reason).to_equal(
    "measurement-qualification-mismatch")
```

</details>

#### requires equal scalar and candidate sample counts

- var pair = perf pair
- pair candidate timed samples ns push


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Avx2)
var pair = perf_pair(qualification, 122000, 72000)
pair.candidate_timed.samples_ns.push(102000)
pair.candidate_timed.sample_set_sha256 =
    x25519_mlkem768_sample_set_sha256(
        pair.candidate_timed.samples_ns)
pair.candidate_timed.full_exchange_count = 31
pair.candidate_timed.hybrid_operation_count = 93
pair.candidate_timed.accelerated_operation_count = 93
pair.candidate_timed.simd_chunk_hits = 93
pair.candidate_timed.receipt_sha256 =
    x25519_mlkem768_timed_operation_receipt_sha256(
        pair.candidate_timed)
val timing_sha256 = x25519_mlkem768_qualified_timing_sha256(
    qualification, pair.scalar_warm, pair.candidate_warm,
    pair.scalar_timed, pair.candidate_timed, pair.schedule)
pair.scalar.qualified_timing_sha256 = timing_sha256
pair.candidate.qualified_timing_sha256 = timing_sha256
pair.candidate.sample_set_sha256 =
    pair.candidate_timed.sample_set_sha256
pair.candidate.metrics = perf_metrics(
    pair.candidate_warm, pair.candidate_timed)
expect(admit_pair(qualification, pair).reason).to_equal(
    "qualified-timing-sample-count-mismatch")
```

</details>

#### rejects every malformed derived metric boundary before qualification

- var warmups = perf pair
- var p50 = perf pair
- var p95 = perf pair
- var p99 = perf pair
- var p50 order = perf pair
- var p95 order = perf pair
- var speedup overflow = perf pair
- var throughput = perf pair
- var rss = perf pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Avx2)
var warmups = perf_pair(qualification, 122000, 72000)
warmups.candidate.metrics.warmup_count = 1
expect(admit_pair(qualification, warmups).reason).to_equal(
    "invalid-native-full-operation-measurement")
var p50 = perf_pair(qualification, 122000, 72000)
p50.candidate.metrics.p50_us = 0
expect(admit_pair(qualification, p50).reason).to_equal(
    "invalid-native-full-operation-measurement")
var p95 = perf_pair(qualification, 122000, 72000)
p95.candidate.metrics.p95_us = 0
expect(admit_pair(qualification, p95).reason).to_equal(
    "invalid-native-full-operation-measurement")
var p99 = perf_pair(qualification, 122000, 72000)
p99.candidate.metrics.p99_us = 0
expect(admit_pair(qualification, p99).reason).to_equal(
    "invalid-native-full-operation-measurement")
var p50_order = perf_pair(qualification, 122000, 72000)
p50_order.candidate.metrics.p50_us =
    p50_order.candidate.metrics.p95_us + 1
expect(admit_pair(qualification, p50_order).reason).to_equal(
    "invalid-native-full-operation-measurement")
var p95_order = perf_pair(qualification, 122000, 72000)
p95_order.candidate.metrics.p99_us =
    p95_order.candidate.metrics.p95_us - 1
expect(admit_pair(qualification, p95_order).reason).to_equal(
    "invalid-native-full-operation-measurement")
var speedup_overflow = perf_pair(qualification, 122000, 72000)
speedup_overflow.scalar.metrics.p95_us = 9223372036854776
speedup_overflow.scalar.metrics.p99_us = 9223372036854776
expect(admit_pair(qualification, speedup_overflow).reason).to_equal(
    "invalid-native-full-operation-measurement")
var throughput = perf_pair(qualification, 122000, 72000)
throughput.candidate.metrics.operations_per_second = 0
expect(admit_pair(qualification, throughput).reason).to_equal(
    "invalid-native-full-operation-measurement")
var rss = perf_pair(qualification, 122000, 72000)
rss.candidate.metrics.max_rss_kb = 0
expect(admit_pair(qualification, rss).reason).to_equal(
    "invalid-native-full-operation-measurement")
```

</details>

#### rejects GPU timing that omits transfer launch sync or readback

- var pair = perf pair
- var stale kernel count = perf pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Vulkan)
var pair = perf_pair(qualification, 97000, 72000)
pair.candidate.gpu_readback_included = false
expect(admit_pair(qualification, pair).reason).to_equal(
    "gpu-end-to-end-lifecycle-incomplete")
var stale_kernel_count = perf_pair(qualification, 97000, 72000)
stale_kernel_count.candidate_timed.gpu_kernel_count =
    stale_kernel_count.candidate_timed.gpu_kernel_count + 1
expect(admit_pair(qualification, stale_kernel_count).reason).to_equal(
    "candidate-timed-operations-invalid")
```

</details>

#### rejects altered raw samples and mismatched qualified timing identity

- var altered = perf pair
- var misordered = perf pair
- var identity = perf pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Avx2)
var altered = perf_pair(qualification, 122000, 72000)
altered.candidate_timed.samples_ns[0] = 1
expect(admit_pair(qualification, altered).reason).to_equal(
    "candidate-timed-operations-invalid")
var misordered = perf_pair(qualification, 122000, 72000)
misordered.schedule.ordinal_base = 1
misordered.schedule.receipt_sha256 =
    x25519_mlkem768_paired_schedule_receipt_sha256(
        misordered.schedule)
expect(admit_pair(qualification, misordered).reason).to_equal(
    "qualified-timing-paired-schedule-invalid")
var identity = perf_pair(qualification, 122000, 72000)
identity.candidate.qualified_timing_sha256 = "7" * 64
expect(admit_pair(qualification, identity).reason).to_equal(
    "qualified-timing-sha256-mismatch")
```

</details>

#### changes the canonical receipt when a retained sample-set hash changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    x25519_mlkem768_synthetic_measurement_qualification(
        X25519MlKem768EvidenceBackend.Avx2)
val pair = perf_pair(qualification, 122000, 72000)
val baseline = x25519_mlkem768_performance_receipt_sha256(
    pair.scalar, pair.candidate)
var changed = pair.candidate
changed.sample_set_sha256 = "7" * 64
expect(x25519_mlkem768_performance_receipt_sha256(
    pair.scalar, changed) == baseline).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_performance_attestation_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 qualified performance attestation v5.
- X25519MLKEM768 qualified performance attestation v5

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
