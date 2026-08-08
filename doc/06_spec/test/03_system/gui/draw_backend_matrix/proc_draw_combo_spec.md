# Processing × Drawing combination runs — headless offscreen readback

> `draw_backend_matrix_spec.spl` (this dir) pins ONE drawing backend at a time. This spec instead runs full **processing × drawing COMBINATION** lanes on a headless host, for three combos — **cuda/vulkan**, **vulkan/vulkan**, and **metal/vulkan** (processing / drawing) — across three surfaces plus event handling:

<!-- sdn-diagram:id=proc_draw_combo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proc_draw_combo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proc_draw_combo_spec -> std
proc_draw_combo_spec -> common
proc_draw_combo_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proc_draw_combo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing × Drawing combination runs — headless offscreen readback

`draw_backend_matrix_spec.spl` (this dir) pins ONE drawing backend at a time. This spec instead runs full **processing × drawing COMBINATION** lanes on a headless host, for three combos — **cuda/vulkan**, **vulkan/vulkan**, and **metal/vulkan** (processing / drawing) — across three surfaces plus event handling:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** Implemented |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`draw_backend_matrix_spec.spl` (this dir) pins ONE drawing backend at a time.
This spec instead runs full **processing × drawing COMBINATION** lanes on a
headless host, for three combos — **cuda/vulkan**, **vulkan/vulkan**, and **metal/vulkan**
(processing / drawing) — across three surfaces plus event handling:

1. **2D** — filled rect + line on a real vulkan framebuffer, `read_pixels()`
   absolute oracle.
2. **Web** — a styled-box HTML fixture rendered headlessly through the
   `simple_web_render_html_to_pixels_with_engine2d_backend(..., "vulkan")` lane;
   the box background AND the styled-box border color must both appear in the
   framebuffer (absolute-color oracle).
3. **GUI** — a widget-layer scene (titlebar bar + button rect) drawn through the
   `Engine2D` facade on vulkan, `read_pixels()` absolute oracle.
4. **Event** — a pointer `TouchPress` dispatched through the real
   `process_event` reducer moves `focused_id`; the button is re-rendered and the
   changed pixel flips from the NORMAL color to the FOCUSED color (both frames
   asserted against absolute values), while the background pixel is unchanged.

## Headless strategy (host has no display)

Every lane uses OFFSCREEN readback (`read_pixels()` → P6 PPM) — the established
oracle that needs no window, no `xvfb-run`, no container, no QEMU. Availability
is never a silent skip: a lane whose device is absent asserts the concrete
fail-closed classification instead.

## Honest processing/drawing split

- **cuda processing half** uses the real host probe `probe_cuda_processing()`
  and asserts EITHER outcome honestly, never a silent skip: if a CUDA device is
  present it must report `has_compute` (gate `cuda_2d_render`); if absent it must
  fail-closed with a concrete `feature_gate` (`cuda-device-unavailable` /
  `cuda_runtime` / `cuda_init`) and a non-empty reason. Whichever branch this
  host lands in, the vulkan drawing half runs in the same `it`. (On the host this
  was authored against, the probe reported `Initialized` / `cuda_2d_render`.)
- **vulkan processing half** exercises the payload-gated compute/offload lane
  (`assert_payload_gating(ComputeBackend.Vulkan)`): the reduce value equals the
  CPU oracle (60) in both gate branches while only the payload gate flips
  `ran_on_cpu` — an absolute oracle, not a masquerade.
- **metal processing half** exercises the same payload-gated compute/offload
  lane for `ComputeBackend.Metal`, so Metal cannot disappear from the processing
  matrix on non-macOS hosts.
- **vulkan drawing half** goes through `Engine2D.probe_backend`/
  `create_requested_backend("vulkan")`; if no Vulkan device is present it
  fail-closes on a concrete `reason` (never a silent skip).

## Syntax

`std.spec` matchers only; facades only (no raw `rt_*`); shared
`assert_color_eq` / `read_pixels_ppm` / `assert_payload_gating` helpers reused
from `test/helpers/gpu_draw_event_shared.spl`.

## Coverage matrix

| Processing | Drawing | 2D | GUI | Web | Event |
|------------|---------|----|-----|-----|-------|
| CUDA | Vulkan | real probe or fail-closed | real probe or fail-closed | real probe or fail-closed | real probe or fail-closed |
| Vulkan | Vulkan | payload gate + readback | payload gate + readback | payload gate + PPM oracle | payload gate + reducer-driven re-render |
| Metal | Vulkan | payload gate + readback | payload gate + readback | payload gate + PPM oracle | payload gate + reducer-driven re-render |

## Scenarios

### Processing × Drawing combination runs — headless offscreen (cuda/vulkan, vulkan/vulkan, metal/vulkan)

#### cuda/vulkan — 2D: cuda processing honest probe (device or fail-closed) + vulkan drawing readback

- assert cuda processing half
- vulkan draw scene or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_cuda_processing_half()
vulkan_draw_scene_or_unavailable("2d")
```

</details>

#### vulkan/vulkan — 2D: vulkan payload-gated processing + vulkan drawing readback

- assert vulkan processing half
- vulkan draw scene or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_vulkan_processing_half()
vulkan_draw_scene_or_unavailable("2d")
```

</details>

#### metal/vulkan — 2D: metal payload-gated processing + vulkan drawing readback

- assert metal processing half
- vulkan draw scene or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_metal_processing_half()
vulkan_draw_scene_or_unavailable("2d")
```

</details>

#### cuda/vulkan — GUI widget-layer scene: cuda processing honest probe + vulkan drawing readback

- assert cuda processing half
- vulkan draw scene or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_cuda_processing_half()
vulkan_draw_scene_or_unavailable("gui")
```

</details>

#### vulkan/vulkan — GUI widget-layer scene: vulkan processing + vulkan drawing readback

- assert vulkan processing half
- vulkan draw scene or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_vulkan_processing_half()
vulkan_draw_scene_or_unavailable("gui")
```

</details>

#### metal/vulkan — GUI widget-layer scene: metal processing + vulkan drawing readback

- assert metal processing half
- vulkan draw scene or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_metal_processing_half()
vulkan_draw_scene_or_unavailable("gui")
```

</details>

#### cuda/vulkan — Web: cuda processing honest probe + vulkan-drawn HTML fixture PPM oracle

- assert cuda processing half
- assert web vulkan render


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_cuda_processing_half()
assert_web_vulkan_render()
```

</details>

#### vulkan/vulkan — Web: vulkan processing + vulkan-drawn HTML fixture PPM oracle

- assert vulkan processing half
- assert web vulkan render


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_vulkan_processing_half()
assert_web_vulkan_render()
```

</details>

#### metal/vulkan — Web: metal processing + vulkan-drawn HTML fixture PPM oracle

- assert metal processing half
- assert web vulkan render


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_metal_processing_half()
assert_web_vulkan_render()
```

</details>

#### cuda/vulkan — Event: pointer press moves focus, re-render flips the button pixel

- assert cuda processing half
- assert event render chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_cuda_processing_half()
assert_event_render_chain()
```

</details>

#### vulkan/vulkan — Event: pointer press moves focus, re-render flips the button pixel

- assert vulkan processing half
- assert event render chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_vulkan_processing_half()
assert_event_render_chain()
```

</details>

#### metal/vulkan — Event: pointer press moves focus, re-render flips the button pixel

- assert metal processing half
- assert event render chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_metal_processing_half()
assert_event_render_chain()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md](doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md)


</details>
