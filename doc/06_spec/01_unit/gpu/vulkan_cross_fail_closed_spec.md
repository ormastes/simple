# Vulkan Cross Fail Closed Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Cross Fail Closed Specification

## Scenarios

### Vulkan cross adapter provenance

#### does not self-report live Vulkan initialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/render_2d_vulkan_cross.spl")
expect(source).to_contain("\"vulkan-unavailable\"")
expect(source).to_contain("VulkanCrossRenderer has no live device; use VulkanBackend")
expect(source).to_contain("fn is_vulkan() -> bool:")
expect(source.contains("self.backend == \"vulkan\"")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/vulkan_cross_fail_closed_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vulkan cross adapter provenance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
