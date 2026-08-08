# X25519mlkem768 Safe Boundary Specification

> Tests covering X25519MLKEM768 safe provider boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Safe Boundary Specification

## Scenarios

### X25519MLKEM768 safe provider boundary

#### should reject non-i32 GPU coefficients before artifact access (NFR-013)

- Submit out-of-range coefficients to every GPU provider
- var cuda = X25519MlKem768CudaNttExecutor create
- cuda shutdown
- var metal = X25519MlKem768MetalNttExecutor create
- metal shutdown
- vulkan shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit out-of-range coefficients to every GPU provider")
val invalid = _safe_boundary_i32_overflow_batch()
var cuda = X25519MlKem768CudaNttExecutor.create("missing.ptx")
val cuda_result = x25519_mlkem768_cuda_ntt_execute(cuda, invalid)
expect(cuda_result.completed).to_be(false)
expect(cuda_result.reason).to_equal(
    "cuda-ntt-input-value-out-of-range")
cuda.shutdown()

var metal = X25519MlKem768MetalNttExecutor.create("missing.metal")
match x25519_mlkem768_metal_ntt_execute(metal, invalid):
    case Ok(_): fail("Metal accepted a coefficient outside signed i32")
    case Err(reason): expect(reason).to_equal(
        "metal-ntt-input-value-out-of-range")
metal.shutdown()

var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "", "missing-inverse.spv", "")
match x25519_mlkem768_vulkan_ntt_execute(vulkan, invalid):
    case Ok(_): fail("Vulkan accepted a coefficient outside signed i32")
    case Err(reason): expect(reason).to_equal(
        "vulkan-ntt-input-value-out-of-range")
vulkan.shutdown()
```

</details>

#### should reject non-byte hybrid inputs before crypto dispatch (NFR-013)

- Submit non-byte private key and seed inputs to candidate APIs
-  safe boundary list32
- x25519 mlkem768 default config
-  safe boundary list32


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit non-byte private key and seed inputs to candidate APIs")
match x25519_mlkem768_combine(
        _safe_boundary_list32(256), _safe_boundary_bytes32()):
    case Ok(_): fail("hybrid combine accepted a non-byte ML-KEM secret")
    case Err(reason): expect(reason).to_equal(
        "ML-KEM-768 shared secret contains a non-byte value")

match x25519_mlkem768_keygen(
        x25519_mlkem768_default_config(), _safe_boundary_bytes32(),
        _safe_boundary_list32(256), _safe_boundary_list32(1)):
    case Ok(_): fail("hybrid keygen accepted a non-byte seed")
    case Err(reason): expect(reason).to_equal(
        "X25519MLKEM768 key generation inputs must contain bytes")
```

</details>

#### should confine raw CUDA pointers to one unsafe capsule (NFR-014)

- Inspect the safe provider and its isolated unsafe CUDA capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the safe provider and its isolated unsafe CUDA capsule")
val provider = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl")
val capsule = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_unsafe.spl")
expect(provider.contains("std.nogc_sync_mut.ptr.raw")).to_be(false)
expect(capsule).to_contain("std.nogc_sync_mut.ptr.raw")
expect(capsule).to_contain("if ptr == 0")
expect(capsule).to_contain("batch > 65535")
```

</details>

#### should decode signed i32 readback and validate exact reads (NFR-013)

- Inspect signed readback decoding and exact byte-count guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect signed readback decoding and exact byte-count guards")
for path in [
    "src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl",
    "src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl"]:
    val source = file_read_text(path)
    expect(source).to_contain("unsigned - 4294967296")
    expect(source).to_contain("read_exact")
    expect(source).to_contain("readback-size-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_safe_boundary_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 safe provider boundary.
- X25519MLKEM768 safe provider boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
