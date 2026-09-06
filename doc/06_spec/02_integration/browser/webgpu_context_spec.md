# Webgpu Context Specification

> <details>

<!-- sdn-diagram:id=webgpu_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_context_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Context Specification

## Scenarios

### WebGPU Types

#### GPUAdapterInfo.software

#### returns the Simple software adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = GPUAdapterInfo.software()
expect(info.vendor).to_equal("simple")
```

</details>

#### GPUDeviceLimits.defaults

#### has max_texture_dimension_2d == 8192

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = GPUDeviceLimits.defaults()
expect(limits.max_texture_dimension_2d).to_equal(8192)
```

</details>

#### GPURequestAdapterOptions.default_options

#### has force_fallback_adapter == false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = GPURequestAdapterOptions.default_options()
expect(opts.force_fallback_adapter).to_equal(false)
```

</details>

#### GPUDeviceDescriptor.create

#### has empty required_features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = GPUDeviceDescriptor.create()
expect(desc.required_features.len()).to_equal(0)
```

</details>

#### GPU_FEATURE_SHADER_F16

#### equals shader-f16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GPU_FEATURE_SHADER_F16).to_equal("shader-f16")
```

</details>

#### GPU_POWER_HIGH

#### equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GPU_POWER_HIGH).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/browser/webgpu_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebGPU Types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
