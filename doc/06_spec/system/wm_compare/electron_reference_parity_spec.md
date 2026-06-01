# Electron Reference Parity Specification

## Scenarios

### wm_compare framebuffer baseline/electron reference parity (electron-reference gate — Electron dev-preview reference)

#### solid fill — electron reference clear() matches fb_driver

#### matches framebuffer exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_electron_reference_parity(scene_solid_fill())
expect(r.pass_exact).to_equal(true)
```

</details>

#### fill_rect row edge — exercises [x,x+w) half-open contract on electron reference

#### matches framebuffer exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_electron_reference_parity(scene_fill_rect_row_edge())
expect(r.pass_exact).to_equal(true)
```

</details>

#### text + bg — electron reference draw_char_8x16 bg cells

#### matches framebuffer exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_electron_reference_parity(scene_text_with_bg())
expect(r.pass_exact).to_equal(true)
```

</details>

#### glass blend — CompositorGlassCapable.blend_rect on electron reference

#### matches framebuffer exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_electron_reference_parity(scene_glass_blend())
expect(r.pass_exact).to_equal(true)
```

</details>

#### marks perceptual as diagnostic only

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_electron_reference_parity(scene_glass_blend())
expect(r.perceptual_diagnostic_only).to_equal(true)
expect(r.exact_required).to_equal(true)
expect(r.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### electron reference render harness self-check

#### returns a buffer of the expected length

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val electron_pixels = render_electron_reference(scene_solid_fill())
expect(electron_pixels.len() == 32 * 16).to_equal(true)
```

</details>

#### diffs identical electron reference buffers as exact

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = render_electron_reference(scene_solid_fill())
val b = render_electron_reference(scene_solid_fill())
val r = diff_buffers("electron_reference_self_check", 32u32, 16u32, a, b)
expect(r.pass_exact).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/system/wm_compare/electron_reference_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare framebuffer baseline/electron reference parity (electron-reference gate — Electron dev-preview reference)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

