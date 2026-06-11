# Vk Create Only Specification

> <details>

<!-- sdn-diagram:id=vk_create_only_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vk_create_only_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vk_create_only_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vk_create_only_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vk Create Only Specification

## Scenarios

### create only

#### create works without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend.create()
expect(b.name()).to_equal("vulkan")
```

</details>

#### init crashes?

- var b = VulkanBackend create
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
expect(b.initialized).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/vk_create_only_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- create only

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
