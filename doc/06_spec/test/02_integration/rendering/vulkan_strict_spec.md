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
| 18 | 18 | 0 | 0 |

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
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
