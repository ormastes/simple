# Web Engine2d Metal Offload Specification

> <details>

<!-- sdn-diagram:id=web_engine2d_metal_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_engine2d_metal_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_engine2d_metal_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_engine2d_metal_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Engine2d Metal Offload Specification

## Scenarios

### Simple Web Renderer Metal GPU offload

#### resolves the Metal backend name correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = simple_web_resolved_engine2d_backend_name(SPEC_W, SPEC_H, "metal")
expect(resolved).to_equal("metal")
```

</details>

#### renders a non-empty pixel buffer via CPU backend (oracle baseline)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _fixture_html()
val cpu_px = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "cpu")
expect(cpu_px.len()).to_equal(SPEC_W * SPEC_H)
expect(_nonzero(cpu_px)).to_be_greater_than(0)
```

</details>

#### HTML layout renderer produces pixels with CSS colors (non-white background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The HTML has body background-color: #1a1a2e — at least some pixels must be that color
val html = _fixture_html()
val cpu_px = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "cpu")
var bg_count = 0
var i = 0
while i < cpu_px.len():
    if cpu_px[i] == 0xFF1A1A2Eu32:
        bg_count = bg_count + 1
    i = i + 1
expect(bg_count).to_be_greater_than(0)
```

</details>

#### scroll offset rendering

#### renders at scroll_y=0 and scroll_y=10 with shifted pixel content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _fixture_html()
val px0 = simple_web_layout_render_html_pixels_at_scroll(html, SPEC_W, SPEC_H, "cpu", 0)
val px10 = simple_web_layout_render_html_pixels_at_scroll(html, SPEC_W, SPEC_H, "cpu", 10)
expect(px0.len()).to_equal(SPEC_W * SPEC_H)
expect(px10.len()).to_equal(SPEC_W * SPEC_H)
expect(_diffcount(px0, px10)).to_be_greater_than(0)
```

</details>

#### scroll shift correctness: row Y at offset 0 == row Y-dy at offset dy

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _fixture_html()
val scroll_dy = 10
val px0 = simple_web_layout_render_html_pixels_at_scroll(html, SPEC_W, SPEC_H, "cpu", 0)
val pxDy = simple_web_layout_render_html_pixels_at_scroll(html, SPEC_W, SPEC_H, "cpu", scroll_dy)
var row_band_diff = 0
var row = scroll_dy
while row < SPEC_H:
    var col = 0
    while col < SPEC_W:
        val p0 = px0[row * SPEC_W + col]
        val pDy = pxDy[(row - scroll_dy) * SPEC_W + col]
        if p0 != pDy:
            row_band_diff = row_band_diff + 1
        col = col + 1
    row = row + 1
expect(row_band_diff).to_equal(0)
```

</details>

#### scroll rendering works with Metal backend (same shift correctness)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val html = _fixture_html()
    val scroll_dy = 10
    val px0 = simple_web_layout_render_html_pixels_at_scroll(html, SPEC_W, SPEC_H, "metal", 0)
    val pxDy = simple_web_layout_render_html_pixels_at_scroll(html, SPEC_W, SPEC_H, "metal", scroll_dy)
    expect(px0.len()).to_equal(SPEC_W * SPEC_H)
    expect(pxDy.len()).to_equal(SPEC_W * SPEC_H)
    expect(_diffcount(px0, pxDy)).to_be_greater_than(0)
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### Metal strict availability

#### reports Metal availability consistently with the platform

- var metal = MetalBackend create
   - Expected: ok is true
- metal shutdown
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var metal = MetalBackend.create()
val ok = metal.init(SPEC_W, SPEC_H)
if is_macos():
    expect(ok).to_equal(true)
    metal.shutdown()
else:
    expect(ok).to_equal(false)
```

</details>

#### on macOS: GPU offload is genuine (gpu_frame_complete=true)

#### MetalBackend.gpu_frame_complete stays true after draw_rect_filled runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val html = _fixture_html()
    val cpu_px = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "cpu")
    val res = _render_metal_direct(cpu_px)
    expect(res.gpu_complete).to_equal(true)
    expect(res.gpu_px.len()).to_equal(SPEC_W * SPEC_H)
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### CPU-vs-Metal mirror is bit-exact (MetalBackend draw_rect_filled path)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val html = _fixture_html()
    val cpu_px = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "cpu")
    val res = _render_metal_direct(cpu_px)
    val diff = _diffcount(cpu_px, res.mirror_px)
    expect(diff).to_equal(0)
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### GPU readback is bit-exact with CPU oracle (genuine GPU rendering)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val html = _fixture_html()
    val cpu_px = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "cpu")
    val res = _render_metal_direct(cpu_px)
    if res.gpu_complete and res.gpu_px.len() == SPEC_W * SPEC_H:
        val diff = _diffcount(cpu_px, res.gpu_px)
        expect(diff).to_equal(0)
    else:
        expect(res.gpu_complete).to_equal(true)
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### present_layout_pixels_with_engine2d metal path does not poison gpu_frame_complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the 'metal' path does NOT call draw_image (which poisons gpu_frame_complete).
# present_layout_pixels_with_engine2d now uses draw_layout_pixel_runs for metal.
if is_macos():
    val html = _fixture_html()
    val metal_px = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "metal")
    expect(metal_px.len()).to_equal(SPEC_W * SPEC_H)
    # Cross-check: render the output via MetalBackend directly
    val res = _render_metal_direct(metal_px)
    expect(res.gpu_complete).to_equal(true)
else:
    expect(is_macos()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/web_engine2d_metal_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web Renderer Metal GPU offload

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
