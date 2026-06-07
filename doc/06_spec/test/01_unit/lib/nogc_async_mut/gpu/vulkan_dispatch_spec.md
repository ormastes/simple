# Vulkan Dispatch Specification

> <details>

<!-- sdn-diagram:id=vulkan_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Dispatch Specification

## Scenarios

### Vulkan dispatch table

#### creates a dispatch table with positive handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = vulkan_dispatch_create(1, 1)
expect(h).to_be_greater_than(0)
```

</details>

#### reports swapchain slot present after creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = vulkan_dispatch_create(2, 3)
expect(vulkan_dispatch_has_swapchain(h)).to_equal(true)
```

</details>

#### returns false for swapchain on invalid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vulkan_dispatch_has_swapchain(0)).to_equal(false)
expect(vulkan_dispatch_has_swapchain(-1)).to_equal(false)
```

</details>

#### destroy makes handle unreachable

1. vulkan dispatch destroy
   - Expected: vulkan_dispatch_has_swapchain(h) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = vulkan_dispatch_create(4, 5)
vulkan_dispatch_destroy(h)
expect(vulkan_dispatch_has_swapchain(h)).to_equal(false)
```

</details>

#### two tables get distinct handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = vulkan_dispatch_create(1, 2)
val h2 = vulkan_dispatch_create(3, 4)
expect(h1).to_not_equal(h2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/vulkan_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vulkan dispatch table

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
