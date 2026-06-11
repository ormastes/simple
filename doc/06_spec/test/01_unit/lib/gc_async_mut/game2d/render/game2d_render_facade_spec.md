# Game2d Render Facade Specification

> <details>

<!-- sdn-diagram:id=game2d_render_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_render_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_render_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_render_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Render Facade Specification

## Scenarios

### gc_async_mut game2d render facade

#### re-exports canvas, image, font, and draw mode behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = Image.null()
expect(image.is_null()).to_equal(true)
val err = RenderError.null_image()
expect(err.code).to_equal("GAME-RENDER-001")

expect(GAME2D_FONT_GLYPH_W).to_equal(8)
expect(GAME2D_FONT_GLYPH_H).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/render/game2d_render_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d render facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
