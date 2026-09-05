# X25519mlkem768 Gpu Lifecycle Counter Contract Specification

> Tests covering X25519MLKEM768 GPU lifecycle counters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Lifecycle Counter Contract Specification

## Scenarios

### X25519MLKEM768 GPU lifecycle counters

#### should initialize every backend lifecycle counter to zero

- Construct rejected snapshots without touching GPU hardware
   - Expected: cuda.transfer_count equals `0`
   - Expected: cuda.launch_count equals `0`
   - Expected: cuda.synchronization_count equals `0`
   - Expected: cuda.readback_count equals `0`
   - Expected: vulkan.transfer_count equals `0`
   - Expected: vulkan.launch_count equals `0`
   - Expected: vulkan.synchronization_count equals `0`
   - Expected: vulkan.readback_count equals `0`
   - Expected: metal.transfer_count equals `0`
   - Expected: metal.launch_count equals `0`
   - Expected: metal.synchronization_count equals `0`
   - Expected: metal.readback_count equals `0`
- cuda shutdown
- vulkan shutdown
- metal shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct rejected snapshots without touching GPU hardware")
var cuda = X25519MlKem768CudaNttExecutor.create_binary(
    "missing.cubin", "0" * 64)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "1" * 64,
    "missing-inverse.spv", "2" * 64)
var metal = X25519MlKem768MetalNttExecutor.create_binary(
    "missing.metallib", "3" * 64)
expect(cuda.transfer_count).to_equal(0)
expect(cuda.launch_count).to_equal(0)
expect(cuda.synchronization_count).to_equal(0)
expect(cuda.readback_count).to_equal(0)
expect(vulkan.transfer_count).to_equal(0)
expect(vulkan.launch_count).to_equal(0)
expect(vulkan.synchronization_count).to_equal(0)
expect(vulkan.readback_count).to_equal(0)
expect(metal.transfer_count).to_equal(0)
expect(metal.launch_count).to_equal(0)
expect(metal.synchronization_count).to_equal(0)
expect(metal.readback_count).to_equal(0)
cuda.shutdown()
vulkan.shutdown()
metal.shutdown()
```

</details>

#### should count CUDA lifecycle events at their successful boundaries

- Inspect upload, launch, synchronize, and readback accounting


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect upload, launch, synchronize, and readback accounting")
val source = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl")
val upload = source.index_of("executor.session.upload(")
val transfer = source.index_of(
    "executor.transfer_count = executor.transfer_count + 1")
val launch = source.index_of(
    "executor.launch_count = executor.launch_count + 1")
val synchronization = source.index_of(
    "executor.synchronization_count = executor.synchronization_count + 1")
val readback = source.index_of(
    "executor.readback_count = executor.readback_count + 1")
val admitted = source.index_of(
    "executor.kernel_invocations = executor.kernel_invocations + 1")
expect(transfer).to_be_greater_than(upload)
expect(launch).to_be_greater_than(transfer)
expect(synchronization).to_be_greater_than(launch)
expect(readback).to_be_greater_than(synchronization)
expect(admitted).to_be_greater_than(readback)
```

</details>

#### should count Vulkan and Metal only after complete device execution

- Keep partial or unknown completion out of promotable counters
- "val bytes = match self session execute


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep partial or unknown completion out of promotable counters")
val vulkan = file_read_text(
    "src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl")
val metal = file_read_text(
    "src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl")
val vulkan_execute = vulkan.index_of("val output = match self.session.execute(")
val vulkan_transfer = vulkan.index_of(
    "self.transfer_count = self.transfer_count + 1")
val vulkan_admitted = vulkan.index_of(
    "self.kernel_invocations = self.kernel_invocations + 1")
expect(vulkan_transfer).to_be_greater_than(vulkan_execute)
expect(vulkan_admitted).to_be_greater_than(vulkan_transfer)
val metal_execute = metal.index_of(
    "val bytes = match self.session.execute(")
val metal_transfer = metal.index_of(
    "self.transfer_count = self.transfer_count + 1")
val metal_admitted = metal.index_of(
    "self.kernel_invocations = self.kernel_invocations + 1")
expect(metal_transfer).to_be_greater_than(metal_execute)
expect(metal_admitted).to_be_greater_than(metal_transfer)
expect(vulkan).to_contain(
    "self.synchronization_count = self.synchronization_count + 1")
expect(vulkan).to_contain(
    "self.readback_count = self.readback_count + 1")
expect(metal).to_contain(
    "self.synchronization_count = self.synchronization_count + 1")
expect(metal).to_contain(
    "self.readback_count = self.readback_count + 1")
```

</details>

#### should terminate every executor before a lifecycle counter can overflow

- Set one public test seam to i64 maximum and execute no GPU work
   - Expected: cuda.closed is true
   - Expected: vulkan.closed is true
   - Expected: metal.closed is true
   - Expected: cuda.transfer_count equals `9223372036854775807`
   - Expected: vulkan.launch_count equals `9223372036854775807`
   - Expected: metal.readback_count equals `9223372036854775807`
- cuda shutdown
- vulkan shutdown
- metal shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set one public test seam to i64 maximum and execute no GPU work")
val fixture = _gpu_lifecycle_counter_fixture()
var cuda = X25519MlKem768CudaNttExecutor.create_binary(
    "missing.cubin", "0" * 64)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "1" * 64,
    "missing-inverse.spv", "2" * 64)
var metal = X25519MlKem768MetalNttExecutor.create_binary(
    "missing.metallib", "3" * 64)
cuda.transfer_count = 9223372036854775807
vulkan.launch_count = 9223372036854775807
metal.readback_count = 9223372036854775807
val cuda_result = x25519_mlkem768_cuda_ntt_execute(cuda, fixture)
val vulkan_reason = match x25519_mlkem768_vulkan_ntt_execute(
        vulkan, fixture):
    case Err(reason): reason
    case Ok(_): "unexpected-success"
val metal_reason = match x25519_mlkem768_metal_ntt_execute(
        metal, fixture):
    case Err(reason): reason
    case Ok(_): "unexpected-success"
expect(cuda_result.reason).to_equal(
    "cuda-ntt-lifecycle-counter-overflow")
expect(vulkan_reason).to_equal(
    "vulkan-ntt-lifecycle-counter-overflow")
expect(metal_reason).to_equal(
    "metal-ntt-lifecycle-counter-overflow")
expect(cuda.closed).to_equal(true)
expect(vulkan.closed).to_equal(true)
expect(metal.closed).to_equal(true)
expect(cuda.transfer_count).to_equal(9223372036854775807)
expect(vulkan.launch_count).to_equal(9223372036854775807)
expect(metal.readback_count).to_equal(9223372036854775807)
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
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_lifecycle_counter_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 GPU lifecycle counters.
- X25519MLKEM768 GPU lifecycle counters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
