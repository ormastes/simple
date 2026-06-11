# Vk Err Mini Specification

> <details>

<!-- sdn-diagram:id=vk_err_mini_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vk_err_mini_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vk_err_mini_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vk_err_mini_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vk Err Mini Specification

## Scenarios

### mini enum

#### enum None works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = VulkanErrorKind.None
expect(k).to_equal(VulkanErrorKind.None)
```

</details>

#### classify empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = vulkan_classify_error("")
expect(k).to_equal(VulkanErrorKind.None)
```

</details>

#### classify device lost

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = vulkan_classify_error("device lost")
expect(k).to_equal(VulkanErrorKind.DeviceLost)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/vk_err_mini_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mini enum

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
