# Processing × Drawing combination runs — headless offscreen readback

> `draw_backend_matrix_spec.spl` (this dir) pins ONE drawing backend at a time. This spec instead runs full **processing × drawing COMBINATION** lanes on a headless host, for three combos — **cuda/vulkan**, **vulkan/vulkan**, and **metal/vulkan** (processing / drawing) — across three surfaces plus event handling:

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cuda/vulkan — 2D: cuda processing honest probe (device or fail-closed) + vulkan drawing readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cuda/vulkan — 2D: cuda processing honest probe (device or fail-closed) + vulkan drawing readback")
assert_cuda_processing_half()
vulkan_draw_scene_or_unavailable("2d")
```

</details>

#### vulkan/vulkan — 2D: vulkan payload-gated processing + vulkan drawing readback

- vulkan/vulkan — 2D: vulkan payload-gated processing + vulkan drawing readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vulkan/vulkan — 2D: vulkan payload-gated processing + vulkan drawing readback")
assert_vulkan_processing_half()
vulkan_draw_scene_or_unavailable("2d")
```

</details>

#### metal/vulkan — 2D: metal payload-gated processing + vulkan drawing readback

- metal/vulkan — 2D: metal payload-gated processing + vulkan drawing readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("metal/vulkan — 2D: metal payload-gated processing + vulkan drawing readback")
assert_metal_processing_half()
vulkan_draw_scene_or_unavailable("2d")
```

</details>

#### cuda/vulkan — GUI widget-layer scene: cuda processing honest probe + vulkan drawing readback

- cuda/vulkan — GUI widget-layer scene: cuda processing honest probe + vulkan drawing readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cuda/vulkan — GUI widget-layer scene: cuda processing honest probe + vulkan drawing readback")
assert_cuda_processing_half()
vulkan_draw_scene_or_unavailable("gui")
```

</details>

#### vulkan/vulkan — GUI widget-layer scene: vulkan processing + vulkan drawing readback

- vulkan/vulkan — GUI widget-layer scene: vulkan processing + vulkan drawing readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vulkan/vulkan — GUI widget-layer scene: vulkan processing + vulkan drawing readback")
assert_vulkan_processing_half()
vulkan_draw_scene_or_unavailable("gui")
```

</details>

#### metal/vulkan — GUI widget-layer scene: metal processing + vulkan drawing readback

- metal/vulkan — GUI widget-layer scene: metal processing + vulkan drawing readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("metal/vulkan — GUI widget-layer scene: metal processing + vulkan drawing readback")
assert_metal_processing_half()
vulkan_draw_scene_or_unavailable("gui")
```

</details>

#### cuda/vulkan — Web: cuda processing honest probe + vulkan-drawn HTML fixture PPM oracle

- cuda/vulkan — Web: cuda processing honest probe + vulkan-drawn HTML fixture PPM oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cuda/vulkan — Web: cuda processing honest probe + vulkan-drawn HTML fixture PPM oracle")
assert_cuda_processing_half()
assert_web_vulkan_render()
```

</details>

#### vulkan/vulkan — Web: vulkan processing + vulkan-drawn HTML fixture PPM oracle

- vulkan/vulkan — Web: vulkan processing + vulkan-drawn HTML fixture PPM oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vulkan/vulkan — Web: vulkan processing + vulkan-drawn HTML fixture PPM oracle")
assert_vulkan_processing_half()
assert_web_vulkan_render()
```

</details>

#### metal/vulkan — Web: metal processing + vulkan-drawn HTML fixture PPM oracle

- metal/vulkan — Web: metal processing + vulkan-drawn HTML fixture PPM oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("metal/vulkan — Web: metal processing + vulkan-drawn HTML fixture PPM oracle")
assert_metal_processing_half()
assert_web_vulkan_render()
```

</details>

#### cuda/vulkan — Event: pointer press moves focus, re-render flips the button pixel

- cuda/vulkan — Event: pointer press moves focus, re-render flips the button pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cuda/vulkan — Event: pointer press moves focus, re-render flips the button pixel")
assert_cuda_processing_half()
assert_event_render_chain()
```

</details>

#### vulkan/vulkan — Event: pointer press moves focus, re-render flips the button pixel

- vulkan/vulkan — Event: pointer press moves focus, re-render flips the button pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vulkan/vulkan — Event: pointer press moves focus, re-render flips the button pixel")
assert_vulkan_processing_half()
assert_event_render_chain()
```

</details>

#### metal/vulkan — Event: pointer press moves focus, re-render flips the button pixel

- metal/vulkan — Event: pointer press moves focus, re-render flips the button pixel
- RUN VERDICT reading rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("metal/vulkan — Event: pointer press moves focus, re-render flips the button pixel")
assert_metal_processing_half()
assert_event_render_chain()

step("RUN VERDICT reading rule")
# Deliberately NOT quoting the literal marker tokens: a verdict line that
# contains them is counted by `grep -c` and inflates the very number it
# is explaining.
print "[RUN VERDICT] A green run of this spec does NOT by itself mean a GPU was exercised."
print "[RUN VERDICT] Count the per-lane GPU/PROVEN disclosure lines: those, and only those, are"
print "[RUN VERDICT] frames a device produced (device_readback + handle > 0 + identity > 0 + full frame)."
print "[RUN VERDICT] Every GPU/BRANCH/SKIPPED line proves NOTHING about the GPU path, and a"
print "[RUN VERDICT] '[toctou]' line means the probe's prediction did not survive to the create."
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

- **Plan:** `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f180de9e606dd7e80a7d1ff661608243ff8271b88e8c15546824ffb17732795e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f180de9e606dd7e80a7d1ff661608243ff8271b88e8c15546824ffb17732795e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f180de9e606dd7e80a7d1ff661608243ff8271b88e8c15546824ffb17732795e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl
mirror: doc/06_spec/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl:347:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cuda/vulkan — 2D: cuda processing honest probe (device or fail-closed) + vulkan drawing readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl:353:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vulkan/vulkan — 2D: vulkan payload-gated processing + vulkan drawing readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl:359:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'metal/vulkan — 2D: metal payload-gated processing + vulkan drawing readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
