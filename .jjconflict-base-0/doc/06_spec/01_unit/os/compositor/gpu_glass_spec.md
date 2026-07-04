# Gpu Glass Specification

> _VirtIO-GPU path glass dispatch — native, no rt_gui_*.""_

<!-- sdn-diagram:id=gpu_glass_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_glass_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_glass_spec -> std
gpu_glass_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_glass_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Glass Specification

## Scenarios

### GpuCompositorBackend CompositorGlassCapable (D2 Phase 2 Gpu)
_VirtIO-GPU path glass dispatch — native, no rt_gui_*.""_

#### as_glass_capable
_Backend opts back in to the glass subtrait in Phase 2 Gpu._

#### opts in (returns non-nil, unlike Phase 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend()
val cap = backend.as_glass_capable()
expect(cap != nil).to_equal(true)
```

</details>

#### cap_blend_rect dispatch

#### type-checks against the Gpu backend

1. cap blend rect
   - Expected: backend.as_glass_capable() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend()
if false:
    cap_blend_rect(backend, 0, 0, 4, 4, 0xFF7F7F7Fu32, 128u8)
expect(backend.as_glass_capable() != nil).to_equal(true)
```

</details>

#### cap_blur_region dispatch

#### type-checks against the Gpu backend

1. cap blur region
   - Expected: backend.as_glass_capable() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend()
if false:
    cap_blur_region(backend, 0, 0, 4, 4, 2u32)
expect(backend.as_glass_capable() != nil).to_equal(true)
```

</details>

#### cap_gradient_v dispatch

#### type-checks against the Gpu backend

1. cap gradient v
   - Expected: backend.as_glass_capable() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend()
if false:
    cap_gradient_v(backend, 0, 0, 4, 4, 0xFF000000u32, 0xFFFFFFFFu32)
expect(backend.as_glass_capable() != nil).to_equal(true)
```

</details>

#### cap_read_pixel dispatch

#### type-checks against the Gpu backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend()
if false:
    val _px = cap_read_pixel(backend, 0, 0)
expect(backend.as_glass_capable() != nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/gpu_glass_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuCompositorBackend CompositorGlassCapable (D2 Phase 2 Gpu)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
