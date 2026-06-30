# Backend Parity Specification

> <details>

<!-- sdn-diagram:id=backend_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_parity_spec -> std
backend_parity_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Parity Specification

## Scenarios

### wm_compare framebuffer/software parity

#### solid fill — clear() on both backends

#### produces zero per-channel delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_solid_fill())
expect(r.pass_exact).to_equal(true)
```

</details>

#### marks perceptual as diagnostic only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_solid_fill())
expect(r.perceptual_diagnostic_only).to_equal(true)
expect(r.exact_required).to_equal(true)
expect(r.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### fill_rect on the row edge — exercises [x,x+w) half-open contract

#### row 0 + row h-1 fill_rect matches framebuffer↔software

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_fill_rect_row_edge())
expect(r.pass_exact).to_equal(true)
```

</details>

#### differs in zero pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_fill_rect_row_edge())
expect(r.differing_pixels == 0u32).to_equal(true)
```

</details>

#### text+bg — draw_text background cells match between backends

#### max channel delta on bg cells is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_text_with_bg())
# software reference flat-block glyph stub matches framebuffer baseline bg writes; this
# validates the bg-cell contract, NOT the glyph rasterizer.
expect(r.pass_exact).to_equal(true)
```

</details>

#### glass blend — degraded blend_rect math

#### exact-match blend output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_glass_blend())
expect(r.pass_exact).to_equal(true)
```

</details>

#### requires exact pixels for blend output acceptance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_framebuffer_software_parity(scene_glass_blend())
expect(r.pass_exact).to_equal(true)
```

</details>

#### diff harness self-check

#### reports identical buffers as exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = render_framebuffer_baseline(scene_solid_fill())
val reference = render_software_reference(scene_solid_fill())
val r = diff_buffers("self_check", 32u32, 16u32, baseline, reference)
expect(r.max_channel_delta == 0u32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/backend_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare framebuffer/software parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
