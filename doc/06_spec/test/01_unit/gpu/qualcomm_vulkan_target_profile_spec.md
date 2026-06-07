# Qualcomm Vulkan Target Profile Specification

> <details>

<!-- sdn-diagram:id=qualcomm_vulkan_target_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qualcomm_vulkan_target_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qualcomm_vulkan_target_profile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qualcomm_vulkan_target_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qualcomm Vulkan Target Profile Specification

## Scenarios

### Qualcomm Vulkan target profile

#### supports ARM64 Vulkan profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val supported = qualcomm_supports_target("arm64", 64)
expect(supported).to_equal(true)
```

</details>

#### supports ARM32 Vulkan preparation profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val supported = qualcomm_supports_target("arm32", 32)
expect(supported).to_equal(true)
```

</details>

#### supports mixed ARM32/ARM64 Vulkan preparation profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val supported = qualcomm_supports_target("arm-mixed", 3264)
expect(supported).to_equal(true)
```

</details>

#### rejects unsupported target width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val supported = qualcomm_supports_target("arm64", 32)
expect(supported).to_equal(false)
```

</details>

#### maps ARM64 profile key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = qualcomm_vulkan_profile_key("arm64", 64)
expect(key).to_equal("qualcomm-adreno:vulkan:arm64")
```

</details>

#### maps mixed ARM profile key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = qualcomm_vulkan_profile_key("arm-mixed", 3264)
expect(key).to_equal("qualcomm-adreno:vulkan:arm32+arm64")
```

</details>

#### prefers Vulkan for supported Qualcomm targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = qualcomm_preferred_backend_for_target("arm64", 64)
expect(backend).to_equal("vulkan")
```

</details>

#### falls back to CPU for unsupported Qualcomm targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = qualcomm_preferred_backend_for_target("x86", 64)
expect(backend).to_equal("cpu")
```

</details>

#### keeps Adreno workgroup and subgroup tuning consistent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qualcomm_preferred_workgroup_size()).to_equal(64)
expect(qualcomm_subgroup_size()).to_equal(64)
```

</details>

#### creates an ARM64 target-profiled backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = QualcommBackend.create_for_target("arm64", 64)
expect(backend.target_arch()).to_equal("arm64")
expect(backend.target_bits()).to_equal(64)
expect(backend.mixed_32_64()).to_equal(false)
expect(backend.target_profile()).to_equal("qualcomm-adreno:vulkan:arm64")
```

</details>

#### creates a mixed ARM target-profiled backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = QualcommBackend.create_for_target("arm-mixed", 3264)
expect(backend.target_arch()).to_equal("arm-mixed")
expect(backend.target_bits()).to_equal(3264)
expect(backend.mixed_32_64()).to_equal(true)
expect(backend.target_profile()).to_equal("qualcomm-adreno:vulkan:arm32+arm64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/qualcomm_vulkan_target_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Qualcomm Vulkan target profile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
