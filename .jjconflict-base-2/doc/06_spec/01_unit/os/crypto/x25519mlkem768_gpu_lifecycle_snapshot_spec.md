# X25519mlkem768 Gpu Lifecycle Snapshot Specification

> Tests covering X25519MLKEM768 typed GPU lifecycle snapshots.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Lifecycle Snapshot Specification

## Scenarios

### X25519MLKEM768 typed GPU lifecycle snapshots

#### accepts finite nonnegative snapshots and rejects every negative field

- Validate each typed counter independently before subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate each typed counter independently before subtraction")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 1, 2, 3, 4))).to_equal("")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(-1, 0, 0, 0, 0))).to_equal(
        "gpu-lifecycle-transfer-negative")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, -1, 0, 0, 0))).to_equal(
        "gpu-lifecycle-launch-negative")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 0, -1, 0, 0))).to_equal(
        "gpu-lifecycle-synchronization-negative")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 0, 0, -1, 0))).to_equal(
        "gpu-lifecycle-readback-negative")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 0, 0, 0, -1))).to_equal(
        "gpu-lifecycle-kernel-negative")
```

</details>

#### accepts every representable terminal counter without arithmetic overflow

- Retain i64 maximum as a final snapshot while rejecting later work


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retain i64 maximum as a final snapshot while rejecting later work")
val maximum: i64 = 9223372036854775807
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(maximum, 0, 0, 0, 0))).to_equal("")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, maximum, 0, 0, 0))).to_equal("")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 0, maximum, 0, 0))).to_equal("")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 0, 0, maximum, 0))).to_equal("")
expect(x25519_mlkem768_gpu_lifecycle_snapshot_reason(
    _snapshot(0, 0, 0, 0, maximum))).to_equal("")
```

</details>

#### computes one positive equal delta bound to the kernel delta

- Subtract a monotonic before/after pair without device access
-  snapshot
   - Expected: delta.transfer_count equals `3`
   - Expected: delta.launch_count equals `3`
   - Expected: delta.synchronization_count equals `3`
   - Expected: delta.readback_count equals `3`
   - Expected: delta.kernel_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Subtract a monotonic before/after pair without device access")
val checked = x25519_mlkem768_gpu_lifecycle_delta(
    _snapshot(7, 7, 7, 7, 7), _snapshot(10, 10, 10, 10, 10))
match checked:
    case Ok(delta):
        expect(delta.transfer_count).to_equal(3)
        expect(delta.launch_count).to_equal(3)
        expect(delta.synchronization_count).to_equal(3)
        expect(delta.readback_count).to_equal(3)
        expect(delta.kernel_count).to_equal(3)
        expect(x25519_mlkem768_gpu_lifecycle_delta_valid(
            delta)).to_equal(true)
    case Err(reason): fail("valid lifecycle delta was rejected: " + reason)
```

</details>

#### rejects every independently future baseline field

- Prove monotonicity across all five counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prove monotonicity across all five counters")
val current = _snapshot(4, 4, 4, 4, 4)
expect(_delta_reason(_snapshot(5, 4, 4, 4, 4), current)).to_equal(
    "gpu-lifecycle-transfer-baseline-future")
expect(_delta_reason(_snapshot(4, 5, 4, 4, 4), current)).to_equal(
    "gpu-lifecycle-launch-baseline-future")
expect(_delta_reason(_snapshot(4, 4, 5, 4, 4), current)).to_equal(
    "gpu-lifecycle-synchronization-baseline-future")
expect(_delta_reason(_snapshot(4, 4, 4, 5, 4), current)).to_equal(
    "gpu-lifecycle-readback-baseline-future")
expect(_delta_reason(_snapshot(4, 4, 4, 4, 5), current)).to_equal(
    "gpu-lifecycle-kernel-baseline-future")
```

</details>

#### rejects zero work and every lifecycle-to-kernel mismatch

- Bind transfer, launch, synchronization, and readback to kernels


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind transfer, launch, synchronization, and readback to kernels")
val baseline = _snapshot(10, 10, 10, 10, 10)
expect(_delta_reason(baseline, baseline)).to_equal(
    "gpu-lifecycle-kernel-delta-not-positive")
expect(_delta_reason(baseline,
    _snapshot(11, 12, 12, 12, 12))).to_equal(
        "gpu-lifecycle-transfer-delta-mismatch")
expect(_delta_reason(baseline,
    _snapshot(12, 11, 12, 12, 12))).to_equal(
        "gpu-lifecycle-launch-delta-mismatch")
expect(_delta_reason(baseline,
    _snapshot(12, 12, 11, 12, 12))).to_equal(
        "gpu-lifecycle-synchronization-delta-mismatch")
expect(_delta_reason(baseline,
    _snapshot(12, 12, 12, 11, 12))).to_equal(
        "gpu-lifecycle-readback-delta-mismatch")
```

</details>

#### rejects invalid baseline and current snapshots before delta math

- Preserve which side supplied malformed or wrapped evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve which side supplied malformed or wrapped evidence")
expect(_delta_reason(_snapshot(-1, 0, 0, 0, 0),
    _snapshot(1, 1, 1, 1, 1))).to_equal(
        "gpu-lifecycle-baseline-invalid:gpu-lifecycle-transfer-negative")
expect(_delta_reason(_snapshot(0, 0, 0, 0, 0),
    _snapshot(0, 0, 0, 0, -1))).to_equal(
        "gpu-lifecycle-current-invalid:gpu-lifecycle-kernel-negative")
```

</details>

#### keeps the standalone delta predicate fail closed on every field

- Exercise predicate branches independently of checked subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise predicate branches independently of checked subtraction")
expect(x25519_mlkem768_gpu_lifecycle_delta_valid(
    X25519MlKem768GpuLifecycleDelta(
        transfer_count: 0, launch_count: 0,
        synchronization_count: 0, readback_count: 0,
        kernel_count: 0))).to_equal(false)
expect(x25519_mlkem768_gpu_lifecycle_delta_valid(
    X25519MlKem768GpuLifecycleDelta(
        transfer_count: 1, launch_count: 2,
        synchronization_count: 2, readback_count: 2,
        kernel_count: 2))).to_equal(false)
expect(x25519_mlkem768_gpu_lifecycle_delta_valid(
    X25519MlKem768GpuLifecycleDelta(
        transfer_count: 2, launch_count: 1,
        synchronization_count: 2, readback_count: 2,
        kernel_count: 2))).to_equal(false)
expect(x25519_mlkem768_gpu_lifecycle_delta_valid(
    X25519MlKem768GpuLifecycleDelta(
        transfer_count: 2, launch_count: 2,
        synchronization_count: 1, readback_count: 2,
        kernel_count: 2))).to_equal(false)
expect(x25519_mlkem768_gpu_lifecycle_delta_valid(
    X25519MlKem768GpuLifecycleDelta(
        transfer_count: 2, launch_count: 2,
        synchronization_count: 2, readback_count: 1,
        kernel_count: 2))).to_equal(false)
```

</details>

#### projects typed snapshots read-only from all three executors

- Read CUDA, Vulkan, and Metal counters through one stable API
   - Expected: cuda_snapshot.transfer_count equals `1`
   - Expected: cuda_snapshot.kernel_count equals `5`
   - Expected: vulkan_snapshot.synchronization_count equals `8`
   - Expected: vulkan_snapshot.kernel_count equals `10`
   - Expected: metal_snapshot.readback_count equals `14`
   - Expected: metal_snapshot.kernel_count equals `15`
- cuda shutdown
- vulkan shutdown
- metal shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read CUDA, Vulkan, and Metal counters through one stable API")
var cuda = X25519MlKem768CudaNttExecutor.create_binary(
    "missing.cubin", "0" * 64)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "1" * 64,
    "missing-inverse.spv", "2" * 64)
var metal = X25519MlKem768MetalNttExecutor.create_binary(
    "missing.metallib", "3" * 64)
cuda.transfer_count = 1
cuda.launch_count = 2
cuda.synchronization_count = 3
cuda.readback_count = 4
cuda.kernel_invocations = 5
vulkan.transfer_count = 6
vulkan.launch_count = 7
vulkan.synchronization_count = 8
vulkan.readback_count = 9
vulkan.kernel_invocations = 10
metal.transfer_count = 11
metal.launch_count = 12
metal.synchronization_count = 13
metal.readback_count = 14
metal.kernel_invocations = 15
val cuda_snapshot = cuda.lifecycle_snapshot()
val vulkan_snapshot = vulkan.lifecycle_snapshot()
val metal_snapshot = metal.lifecycle_snapshot()
expect(cuda_snapshot.transfer_count).to_equal(1)
expect(cuda_snapshot.kernel_count).to_equal(5)
expect(vulkan_snapshot.synchronization_count).to_equal(8)
expect(vulkan_snapshot.kernel_count).to_equal(10)
expect(metal_snapshot.readback_count).to_equal(14)
expect(metal_snapshot.kernel_count).to_equal(15)
cuda.shutdown()
vulkan.shutdown()
metal.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_lifecycle_snapshot_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 typed GPU lifecycle snapshots.
- X25519MLKEM768 typed GPU lifecycle snapshots

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
