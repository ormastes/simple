# Text Render Specification

> 1. draw text at

<!-- sdn-diagram:id=text_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_render_spec -> std
text_render_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Render Specification

## Scenarios

### text_render

#### draw_text_at renders non-ascii text through the shared renderer

1. draw text at
   - Expected: _non_clear_pixels(pixels) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = BrowserCompositorBackend.with_color(W, H, CLEAR)
draw_text_at(backend, 4, 4, "あ", 0xFFFFFFFF)
val pixels = backend.get_pixel_buffer()
expect(_non_clear_pixels(pixels) > 0).to_equal(true)
```

</details>

#### draw_text_scaled increases rendered ink area at larger scale

1. draw text scaled
2. draw text scaled
   - Expected: large_ink > small_ink is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val small = BrowserCompositorBackend.with_color(W, H, CLEAR)
val large = BrowserCompositorBackend.with_color(W, H, CLEAR)
draw_text_scaled(small, 4, 4, "A", 0xFFFFFFFF, 1)
draw_text_scaled(large, 4, 4, "A", 0xFFFFFFFF, 2)
val small_ink = _non_clear_pixels(small.get_pixel_buffer())
val large_ink = _non_clear_pixels(large.get_pixel_buffer())
expect(large_ink > small_ink).to_equal(true)
```

</details>

#### text_width_2x is greater than text_width for the same text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = text_width("Aあ")
val scaled = text_width_2x("Aあ")
expect(scaled > base).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/ui/text_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- text_render

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
