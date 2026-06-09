# Vulkan Strict Specification

> <details>

<!-- sdn-diagram:id=vulkan_strict_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_strict_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_strict_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_strict_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Strict Specification

## Scenarios

### Vulkan strict smoke tests

#### probe_vulkan device diagnostics

#### probe_vulkan returns a typed BackendProbeResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
val ok = probe.is_ok() or status_is_terminal_failure(probe)
expect(ok).to_equal(true)
```

</details>

#### probe_vulkan reports requested_name as vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
expect(probe.requested_name).to_equal("vulkan")
```

</details>

#### probe_vulkan on success reports api_name as vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    expect(probe.api_name).to_equal("vulkan")
```

</details>

#### probe_vulkan on failure carries non-empty fallback_reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if not probe.is_ok():
    expect(probe.fallback_reason).to_not_equal("")
```

</details>

#### probe_vulkan diagnostic_text is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
val txt = probe.diagnostic_text()
expect(txt.len()).to_be_greater_than(0)
```

</details>

#### create_with_backend_strict vulkan unavailable path

#### fails with typed error when Vulkan is not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if not probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    expect(result.is_ok()).to_equal(false)
    val diag = result.unwrap_err()
    val failed_or_unavail = status_is_terminal_failure(diag)
    expect(failed_or_unavail).to_equal(true)
    expect(diag.requested_name).to_equal("vulkan")
```

</details>

#### fallback_reason is non-empty when Vulkan fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if not probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if not result.is_ok():
        val diag = result.unwrap_err()
        expect(diag.fallback_reason).to_not_equal("")
```

</details>

#### does not silently fall back to cpu on Vulkan failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if not probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    expect(result.is_ok()).to_equal(false)
```

</details>

#### create_with_backend_strict vulkan hardware path

#### succeeds and returns Engine2D when hardware available

- var engine = result unwrap
   - Expected: engine.width() equals `16`
   - Expected: engine.height() equals `16`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    expect(result.is_ok()).to_equal(true)
    var engine = result.unwrap()
    expect(engine.width()).to_equal(16)
    expect(engine.height()).to_equal(16)
    engine.shutdown()
```

</details>

#### backend_name is vulkan when hardware available

- var engine = result unwrap
   - Expected: engine.backend_name() equals `vulkan`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        expect(engine.backend_name()).to_equal("vulkan")
        engine.shutdown()
```

</details>

#### SPIR-V shader modules load without error when hardware available

- var engine = result unwrap
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    # A successful init() implies all spirv_* blobs were accepted by the driver
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    expect(result.is_ok()).to_equal(true)
    if result.is_ok():
        var engine = result.unwrap()
        engine.shutdown()
```

</details>

#### clear pixel parity with CPU reference

#### clear fills entire framebuffer with the given color

- var engine = result unwrap
- engine clear
- engine present
   - Expected: pixels[0] equals `fill_color`
   - Expected: pixels[127] equals `fill_color`
   - Expected: pixels[255] equals `fill_color`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val fill_color = color_blue_u32()
        engine.clear(fill_color)
        engine.present()
        val pixels = engine.read_pixels()
        # Check first, middle, and last pixel
        expect(pixels[0]).to_equal(fill_color)
        expect(pixels[127]).to_equal(fill_color)
        expect(pixels[255]).to_equal(fill_color)
        engine.shutdown()
```

</details>

#### clear matches CPU reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine present
   - Expected: mismatch_count equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val fill_color = color_blue_u32()
        engine.clear(fill_color)
        engine.present()
        val pixels = engine.read_pixels()
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            if pixels[ci] != fill_color:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_rect_filled pixel parity with CPU reference

#### draw_rect_filled writes correct pixels in the rect region

- var engine = result unwrap
- engine clear
- engine draw rect filled
- engine present
   - Expected: inside equals `fg`
   - Expected: outside equals `bg`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        # Clear to blue, draw 4x4 red rect at (4,4)
        engine.clear(bg)
        engine.draw_rect_filled(4, 4, 4, 4, fg)
        engine.present()
        val pixels = engine.read_pixels()
        # Pixel at (6,6) must be inside the rect (red)
        val inside = pixels[6 * 16 + 6]
        expect(inside).to_equal(fg)
        # Pixel at (0,0) must be outside rect (blue)
        val outside = pixels[0]
        expect(outside).to_equal(bg)
        engine.shutdown()
```

</details>

#### clear then draw_rect_filled matches CPU reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rect filled
- engine present
   - Expected: mismatch_count equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rect_filled(2, 2, 6, 6, fg)
        engine.present()
        val pixels = engine.read_pixels()
        # Build CPU reference
        val cpu_ref = build_cpu_reference(16, 16, bg, fg, 2, 2, 6, 6)
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            if pixels[ci] != cpu_ref[ci]:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
        engine.shutdown()
```

</details>

#### rect outside framebuffer bounds does not corrupt surrounding pixels

- var engine = result unwrap
- engine clear
- engine draw rect filled
- engine present
   - Expected: pixels[0] equals `bg`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        # Draw rect that starts at (14,14) with size (8,8) — mostly out of bounds
        engine.draw_rect_filled(14, 14, 8, 8, fg)
        engine.present()
        val pixels = engine.read_pixels()
        # Pixel at (0,0) must still be blue
        expect(pixels[0]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_rect outline pixel parity with CPU reference

#### draw_rect writes only the rectangle border

- var engine = result unwrap
- engine clear
- engine draw rect
- engine present
   - Expected: pixels[4 * 16 + 4] equals `fg`
   - Expected: pixels[6 * 16 + 6] equals `bg`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rect(4, 4, 6, 6, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels[4 * 16 + 4]).to_equal(fg)
        expect(pixels[6 * 16 + 6]).to_equal(bg)
        engine.shutdown()
```

</details>

#### clear then draw_rect matches CPU outline reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rect
- engine present
   - Expected: mismatch_count equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rect(3, 2, 7, 5, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val cpu_ref = build_cpu_rect_outline_reference(16, 16, bg, fg, 3, 2, 7, 5)
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            if pixels[ci] != cpu_ref[ci]:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_line pixel parity with CPU reference

#### draw_line writes expected diagonal endpoints and center

- var engine = result unwrap
- engine clear
- engine draw line
- engine present
   - Expected: pixels[2 * 16 + 2] equals `fg`
   - Expected: pixels[6 * 16 + 6] equals `fg`
   - Expected: pixels[10 * 16 + 10] equals `fg`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_line(2, 2, 10, 10, fg, 1)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels[2 * 16 + 2]).to_equal(fg)
        expect(pixels[6 * 16 + 6]).to_equal(fg)
        expect(pixels[10 * 16 + 10]).to_equal(fg)
        engine.shutdown()
```

</details>

#### clear then draw_line matches CPU reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw line
- engine present
   - Expected: mismatch_count equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_line(1, 13, 12, 4, fg, 1)
        engine.present()
        val pixels = engine.read_pixels()
        val cpu_ref = build_cpu_line_reference(16, 16, bg, fg, 1, 13, 12, 4)
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            if pixels[ci] != cpu_ref[ci]:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
        engine.shutdown()
```

</details>

#### additional GPU raster parity

#### draw_circle outline matches the Vulkan kernel reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw circle
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_circle(8, 8, 4, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = build_cpu_circle_outline_reference(16, 16, bg, fg, 8, 8, 4)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_circle_filled matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw circle filled
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_circle_filled(7, 8, 3, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_circle_reference(bg, fg, 7, 8, 3)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_rounded_rect matches the Vulkan kernel reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rounded rect
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rounded_rect(2, 3, 10, 8, 2, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = build_cpu_rounded_rect_reference(16, 16, bg, fg, 2, 3, 10, 8, 2)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_triangle_filled matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw triangle filled
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_triangle_filled(8, 2, 3, 11, 12, 13, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_triangle_reference(bg, fg, 8, 2, 3, 11, 12, 13)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_gradient_rect matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw gradient rect
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val top = color_red_u32()
        val bottom = 0xFF00FF00u32
        engine.clear(bg)
        engine.draw_gradient_rect(4, 2, 7, 10, top, bottom)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_gradient_reference(bg, 4, 2, 7, 10, top, bottom)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_gradient_rect_h matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw gradient rect h
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val left = color_red_u32()
        val right = 0xFF00FF00u32
        engine.clear(bg)
        engine.draw_gradient_rect_h(2, 5, 8, 4, left, right)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_gradient_h_reference(bg, 2, 5, 8, 4, left, right)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_radial_gradient matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw radial gradient
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val center = 0xFFFFFFFFu32
        val edge = 0xFF0000FFu32
        engine.clear(bg)
        engine.draw_radial_gradient(8, 8, 4, center, edge)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_radial_gradient_reference(bg, 8, 8, 4, center, edge)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_rect_blend matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rect blend
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = 0xff204060u32
        val fg = 0x80ff0000u32
        engine.clear(bg)
        engine.draw_rect_blend(3, 4, 5, 3, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_rect_blend_reference(bg, 3, 4, 5, 3, fg)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_image_blend matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw image blend
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = 0xff204060u32
        val src = [
            0x80ff0000u32, 0x8000ff00u32,
            0x800000ffu32, 0x80ffffffu32
        ]
        engine.clear(bg)
        engine.draw_image_blend(4, 5, 2, 2, src)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_image_blend_reference(bg, 4, 5, 2, 2, src)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_rect_blend_mode matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rect blend mode
- engine present
- var pixels = engine read pixels
- var ref = render software rect blend mode reference
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine clear
- engine draw rect blend mode
- engine present
- pixels = engine read pixels
- ref = render software rect blend mode reference
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = 0xff204060u32
        val fg = 0x80ff0000u32
        engine.clear(bg)
        engine.draw_rect_blend_mode(3, 4, 5, 3, fg, 1)
        engine.present()
        var pixels = engine.read_pixels()
        var ref = render_software_rect_blend_mode_reference(bg, 3, 4, 5, 3, fg, 1)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)

        engine.clear(bg)
        engine.draw_rect_blend_mode(3, 4, 5, 3, fg, 3)
        engine.present()
        pixels = engine.read_pixels()
        ref = render_software_rect_blend_mode_reference(bg, 3, 4, 5, 3, fg, 3)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_polyline matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw polyline
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        val xs = [1, 5, 9, 13]
        val ys = [12, 4, 10, 3]
        engine.clear(bg)
        engine.draw_polyline(xs, ys, 4, fg, 1)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = build_cpu_polyline_reference(16, 16, bg, fg, xs, ys, 4)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_rect_thick matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rect thick
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rect_thick(2, 3, 10, 8, fg, 2)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_rect_thick_reference(bg, fg, 2, 3, 10, 8, 2)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_triangle_outline matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw triangle outline
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_triangle_outline(8, 2, 3, 11, 12, 13, fg, 1)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_triangle_outline_reference(bg, fg, 8, 2, 3, 11, 12, 13, 1)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_image matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw image
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val src = [
            0xFFFF0000u32, 0xFF00FF00u32, 0xFF0000FFu32,
            0xFFFFFF00u32, 0xFFFF00FFu32, 0xFF00FFFFu32
        ]
        engine.clear(bg)
        engine.draw_image(5, 4, 3, 2, src)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_image_reference(bg, 5, 4, 3, 2, src)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_circle_thick matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw circle thick
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_circle_thick(12, 12, 5, fg, 2)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_circle_thick_reference(bg, fg, 12, 12, 5, 2)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_rounded_rect_outline matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rounded rect outline
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rounded_rect_outline(4, 5, 12, 10, 3, fg, 2)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_rounded_rect_outline_reference(bg, fg, 4, 5, 12, 10, 3, 2)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_ellipse matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw ellipse
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_ellipse(12, 12, 5, 3, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_ellipse_reference(bg, fg, 12, 12, 5, 3)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_ellipse_filled matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw ellipse filled
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_ellipse_filled(12, 12, 5, 3, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_ellipse_filled_reference(bg, fg, 12, 12, 5, 3)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_arc matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw arc
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_arc(12, 12, 6, 30, 160, fg, 2)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_arc_reference(bg, fg, 12, 12, 6, 30, 160, 2)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_bezier matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw bezier
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_bezier(2, 18, 6, 2, 18, 4, 21, 18, fg, 1)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_bezier_reference(bg, fg, 2, 18, 6, 2, 18, 4, 21, 18, 1)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_polygon_filled matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw polygon filled
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        val xs = [4, 12, 19, 15, 7]
        val ys = [18, 4, 8, 19, 16]
        engine.clear(bg)
        engine.draw_polygon_filled(xs, ys, 5, fg)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_polygon_filled_reference(bg, fg, xs, ys, 5)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_image_transform matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw image transform
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(32, 32, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val src = [
            0xFFFF0000u32, 0xFF00FF00u32, 0xFF0000FFu32,
            0xFFFFFF00u32, 0xFFFF00FFu32, 0xFF00FFFFu32
        ]
        engine.clear(bg)
        engine.draw_image_transform(10, 10, 3, 2, 256, 64, 0, 256, 0, 0, src)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_image_transform_reference(bg, 10, 10, 3, 2, 256, 64, 0, 256, 0, 0, src)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_blur_rect matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw rect filled
- engine draw blur rect
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        engine.clear(bg)
        engine.draw_rect_filled(6, 6, 8, 6, 0xFFFF0000u32)
        engine.draw_blur_rect(6, 6, 8, 6, 2)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_blur_rect_reference(bg, 6, 6, 8, 6, 2)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_shadow_rect matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw shadow rect
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(32, 32, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val shadow = 0x80202020u32
        engine.clear(bg)
        engine.draw_shadow_rect(8, 8, 6, 5, 2, 2, 2, shadow)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_shadow_rect_reference(bg, 8, 8, 6, 5, 2, 2, 2, shadow)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### clipped draw_rect_filled matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine set clip
- engine draw rect filled
- engine clear clip
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = 0xff000000u32
        val fg = 0xffff0000u32
        engine.clear(bg)
        engine.set_clip(4, 4, 6, 4)
        engine.draw_rect_filled(2, 4, 10, 3, fg)
        engine.clear_clip()
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_clip_rect_reference(bg, fg, 4, 4, 6, 4, 2, 4, 10, 3)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### masked draw_rect_filled matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine set mask
- engine draw rect filled
- engine clear mask
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = 0xff000000u32
        val fg = 0xff3366ccu32
        val mask = [
            0u8, 0u8, 0u8, 0u8,
            0u8, 1u8, 1u8, 0u8,
            0u8, 1u8, 1u8, 0u8,
            0u8, 0u8, 0u8, 0u8
        ]
        engine.clear(bg)
        engine.set_mask(mask, 4, 4)
        engine.draw_rect_filled(1, 1, 4, 4, fg)
        engine.clear_mask()
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_mask_rect_reference(bg, fg, mask, 4, 4, 1, 1, 4, 4)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### masked draw_image matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine set mask
- engine draw image
- engine clear mask
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(24, 24, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = 0xff000000u32
        val mask = [
            0u8, 0u8, 0u8, 0u8,
            0u8, 1u8, 1u8, 0u8,
            0u8, 1u8, 1u8, 0u8,
            0u8, 0u8, 0u8, 0u8
        ]
        val src = [
            0xff0000ffu32, 0xff00ff00u32,
            0xffff0000u32, 0xffffffffu32
        ]
        engine.clear(bg)
        engine.set_mask(mask, 4, 4)
        engine.draw_image(1, 1, 2, 2, src)
        engine.clear_mask()
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_mask_image_reference(bg, mask, 4, 4, 1, 1, 2, 2, src)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_text matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw text
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(32, 32, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_text(3, 4, "Hi", fg, 8)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_text_reference(bg, 3, 4, "Hi", fg, 8)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_text_bg matches software reference pixel-for-pixel

- var engine = result unwrap
- engine clear
- engine draw text bg
- engine present
   - Expected: count_pixel_mismatches(pixels, ref) equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(32, 32, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        val fill = 0xFF202020u32
        engine.clear(bg)
        engine.draw_text_bg(3, 4, "Hi", fg, fill, 8)
        engine.present()
        val pixels = engine.read_pixels()
        val ref = render_software_text_bg_reference(bg, 3, 4, "Hi", fg, fill, 8)
        expect(count_pixel_mismatches(pixels, ref)).to_equal(0)
        engine.shutdown()
```

</details>

#### sync and readback correctness

#### read_pixels after present reflects latest draw

- var engine = result unwrap
- engine clear
- engine present
   - Expected: pixels_first[0] equals `first_color`
- engine clear
- engine present
   - Expected: pixels_second[0] equals `second_color`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val first_color = color_blue_u32()
        val second_color = color_red_u32()
        engine.clear(first_color)
        engine.present()
        val pixels_first = engine.read_pixels()
        expect(pixels_first[0]).to_equal(first_color)
        engine.clear(second_color)
        engine.present()
        val pixels_second = engine.read_pixels()
        expect(pixels_second[0]).to_equal(second_color)
        engine.shutdown()
```

</details>

#### present idempotent — second present same content

- var engine = result unwrap
- engine clear
- engine present
- engine present
   - Expected: p1[0] equals `p2[0]`
   - Expected: p1[255] equals `p2[255]`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_vulkan()
if probe.is_ok():
    val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
    if result.is_ok():
        var engine = result.unwrap()
        val fill_color = color_red_u32()
        engine.clear(fill_color)
        engine.present()
        val p1 = engine.read_pixels()
        engine.present()
        val p2 = engine.read_pixels()
        expect(p1[0]).to_equal(p2[0])
        expect(p1[255]).to_equal(p2[255])
        engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_strict_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vulkan strict smoke tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
