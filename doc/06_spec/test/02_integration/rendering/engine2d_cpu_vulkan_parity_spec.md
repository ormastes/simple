# Engine2d Cpu Vulkan Parity Specification

> <details>

<!-- sdn-diagram:id=engine2d_cpu_vulkan_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_cpu_vulkan_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_cpu_vulkan_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_cpu_vulkan_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Cpu Vulkan Parity Specification

## Scenarios

### Engine2D CPU and Vulkan rendering parity baseline

#### core primitives

#### keeps cpu rendering deterministic

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = render_cpu_vulkan_core_scene("cpu")
val second = render_cpu_vulkan_core_scene("cpu")
expect(parity_pixels_equal(first, second)).to_equal(true)
expect(parity_pixel_at(first, 2, 2, 32)).to_equal(rgb(40, 70, 100))
```

</details>

#### matches the software reference for core primitives

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val software = render_cpu_vulkan_core_scene("software")
val cpu = render_cpu_vulkan_core_scene("cpu")
expect(parity_pixels_equal(software, cpu)).to_equal(true)
```

</details>

#### vulkan availability path

#### creates the Vulkan backend object without resolving the nogc session constructor

1. var backend = VulkanBackend create
   - Expected: backend.name() equals `vulkan`
   - Expected: backend.width() equals `0`
   - Expected: backend.height() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
expect(backend.name()).to_equal("vulkan")
expect(backend.width()).to_equal(0)
expect(backend.height()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_cpu_vulkan_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D CPU and Vulkan rendering parity baseline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
