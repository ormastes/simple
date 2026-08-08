# X25519mlkem768 Artifact Snapshot Admission Specification

> Tests covering X25519MLKEM768 pure accelerator artifact snapshot admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Artifact Snapshot Admission Specification

## Scenarios

### X25519MLKEM768 pure accelerator artifact snapshot admission

#### should NFR-012 enforce CUDA source and binary size boundaries

- Evaluate CUDA artifact sizes without reading a file or opening a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate CUDA artifact sizes without reading a file or opening a device")
expect(x25519_mlkem768_artifact_size_admitted(
    0, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    _SOURCE_MAX_BYTES, _SOURCE_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _SOURCE_MAX_BYTES + 1, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES + 1,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(false)
```

</details>

#### should NFR-012 enforce Metal source and binary size boundaries

- Evaluate Metal artifact sizes without reading a file or opening a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate Metal artifact sizes without reading a file or opening a device")
expect(x25519_mlkem768_artifact_size_admitted(
    -1, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    1, _SOURCE_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _SOURCE_MAX_BYTES + 1, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES + 1,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(false)
```

</details>

#### should NFR-012 enforce Vulkan binary size boundaries

- Evaluate paired SPIR-V artifact sizes without reading a file or opening a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate paired SPIR-V artifact sizes without reading a file or opening a device")
expect(x25519_mlkem768_artifact_size_admitted(
    0, _VULKAN_BINARY_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    1, _VULKAN_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _VULKAN_BINARY_MAX_BYTES,
    _VULKAN_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _VULKAN_BINARY_MAX_BYTES + 1,
    _VULKAN_BINARY_MAX_BYTES)).to_be(false)
```

</details>

#### should NFR-012 reject short and overlong snapshots for every provider

- Compare admitted metadata with exact short and overlong read lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare admitted metadata with exact short and overlong read lengths")
expect(x25519_mlkem768_artifact_read_exact(
    false, 16, 16)).to_be(false)
expect(x25519_mlkem768_artifact_read_exact(
    true, 16, 15)).to_be(false)
expect(x25519_mlkem768_artifact_read_exact(
    true, 16, 16)).to_be(true)
expect(x25519_mlkem768_artifact_read_exact(
    true, 16, 17)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 pure accelerator artifact snapshot admission.
- X25519MLKEM768 pure accelerator artifact snapshot admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
