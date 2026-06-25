# Cuda Strict Specification

> <details>

<!-- sdn-diagram:id=cuda_strict_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_strict_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_strict_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_strict_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Strict Specification

## Scenarios

### CUDA strict smoke tests

#### probe_cuda device diagnostics

#### probe_cuda returns a typed BackendProbeResult

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
val ok = probe.is_usable() or status_is_terminal_failure(probe)
expect(ok).to_equal(true)
```

</details>

#### probe_cuda reports requested_name as cuda

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
expect(probe.requested_name).to_equal("cuda")
```

</details>

#### probe_cuda on success reports device name and ptx shader_format

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    expect(probe.device_name.len()).to_be_greater_than(0)
    expect(probe.shader_format).to_equal("ptx")
    expect(probe.api_name).to_equal("cuda")
```

</details>

#### probe_cuda on failure carries non-empty fallback_reason

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if not probe.is_usable():
    expect(probe.fallback_reason.len()).to_be_greater_than(0)
```

</details>

#### probe_cuda diagnostic_text is non-empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
val txt = probe.diagnostic_text()
expect(txt.len()).to_be_greater_than(0)
```

</details>

#### create_with_backend_strict cuda unavailable path

#### fails with typed error when CUDA is not available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if not probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    expect(result.is_ok()).to_equal(false)
    val diag = result.unwrap_err()
    val failed_or_unavail = status_is_terminal_failure(diag)
    expect(failed_or_unavail).to_equal(true)
    expect(diag.requested_name).to_equal("cuda")
```

</details>

#### fallback_reason is non-empty when CUDA fails

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if not probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if not result.is_ok():
        val diag = result.unwrap_err()
        expect(diag.fallback_reason.len()).to_be_greater_than(0)
```

</details>

#### create_with_backend_strict cuda hardware path

#### succeeds and returns Engine2D when hardware available

1. var engine = result unwrap
   - Expected: engine.width() equals `16`
   - Expected: engine.height() equals `16`

2. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    expect(result.is_ok()).to_equal(true)
    var engine = result.unwrap()
    expect(engine.width()).to_equal(16)
    expect(engine.height()).to_equal(16)
    engine.shutdown()
```

</details>

#### backend_name is cuda when hardware available

1. var engine = result unwrap
   - Expected: engine.backend_name() equals `cuda`

2. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        expect(engine.backend_name()).to_equal("cuda")
        engine.shutdown()
```

</details>

#### PTX kernel: clear and readback

#### clear to red produces all-red pixels

1. var engine = result unwrap

2. engine clear

3. engine present
   - Expected: pixels.len() equals `256`
   - Expected: all_red is true

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val red = color_red_u32()
        engine.clear(red)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        var all_red = true
        var idx = 0
        while idx < 256:
            if pixels[idx] != red:
                all_red = false
            idx = idx + 1
        expect(all_red).to_equal(true)
        engine.shutdown()
```

</details>

#### draw_rect_filled writes correct pixels in the rect region

1. var engine = result unwrap

2. engine clear

3. engine draw rect filled

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: inside equals `fg`
   - Expected: outside equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        # Clear to blue, draw 4x4 red rect at (4,4)
        engine.clear(bg)
        engine.draw_rect_filled(4, 4, 4, 4, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        # Pixel at (6,6) inside rect must be red
        val inside = pixels[6 * 16 + 6]
        expect(inside).to_equal(fg)
        # Pixel at (0,0) outside rect must be blue
        val outside = pixels[0]
        expect(outside).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_rect writes only the outline pixels

1. var engine = result unwrap

2. engine clear

3. engine draw rect

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[4 * 16 + 4] equals `fg`
   - Expected: pixels[4 * 16 + 9] equals `fg`
   - Expected: pixels[8 * 16 + 4] equals `fg`
   - Expected: pixels[8 * 16 + 9] equals `fg`
   - Expected: pixels[6 * 16 + 6] equals `bg`
   - Expected: pixels[0] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rect(4, 4, 6, 5, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[4 * 16 + 4]).to_equal(fg)
        expect(pixels[4 * 16 + 9]).to_equal(fg)
        expect(pixels[8 * 16 + 4]).to_equal(fg)
        expect(pixels[8 * 16 + 9]).to_equal(fg)
        expect(pixels[6 * 16 + 6]).to_equal(bg)
        expect(pixels[0]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_line writes line pixels through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw line

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[2 * 16 + 2] equals `fg`
   - Expected: pixels[2 * 16 + 3] equals `fg`
   - Expected: pixels[2 * 16 + 4] equals `fg`
   - Expected: pixels[2 * 16 + 5] equals `fg`
   - Expected: pixels[2 * 16 + 6] equals `fg`
   - Expected: pixels[3 * 16 + 2] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_line(2, 2, 6, 2, fg, 1)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[2 * 16 + 2]).to_equal(fg)
        expect(pixels[2 * 16 + 3]).to_equal(fg)
        expect(pixels[2 * 16 + 4]).to_equal(fg)
        expect(pixels[2 * 16 + 5]).to_equal(fg)
        expect(pixels[2 * 16 + 6]).to_equal(fg)
        expect(pixels[3 * 16 + 2]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_circle writes outline pixels through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw circle

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[8 * 16 + 11] equals `fg`
   - Expected: pixels[8 * 16 + 5] equals `fg`
   - Expected: pixels[11 * 16 + 8] equals `fg`
   - Expected: pixels[5 * 16 + 8] equals `fg`
   - Expected: pixels[8 * 16 + 8] equals `bg`
   - Expected: pixels[0] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_circle(8, 8, 3, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[8 * 16 + 11]).to_equal(fg)
        expect(pixels[8 * 16 + 5]).to_equal(fg)
        expect(pixels[11 * 16 + 8]).to_equal(fg)
        expect(pixels[5 * 16 + 8]).to_equal(fg)
        expect(pixels[8 * 16 + 8]).to_equal(bg)
        expect(pixels[0]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_circle_filled writes filled pixels through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw circle filled

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[8 * 16 + 8] equals `fg`
   - Expected: pixels[8 * 16 + 11] equals `fg`
   - Expected: pixels[8 * 16 + 5] equals `fg`
   - Expected: pixels[11 * 16 + 8] equals `fg`
   - Expected: pixels[5 * 16 + 8] equals `fg`
   - Expected: pixels[4 * 16 + 4] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_circle_filled(8, 8, 3, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[8 * 16 + 8]).to_equal(fg)
        expect(pixels[8 * 16 + 11]).to_equal(fg)
        expect(pixels[8 * 16 + 5]).to_equal(fg)
        expect(pixels[11 * 16 + 8]).to_equal(fg)
        expect(pixels[5 * 16 + 8]).to_equal(fg)
        expect(pixels[4 * 16 + 4]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_rounded_rect writes rounded fill through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw rounded rect

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[4 * 16 + 4] equals `bg`
   - Expected: pixels[4 * 16 + 5] equals `bg`
   - Expected: pixels[4 * 16 + 6] equals `fg`
   - Expected: pixels[6 * 16 + 4] equals `fg`
   - Expected: pixels[6 * 16 + 8] equals `fg`
   - Expected: pixels[9 * 16 + 11] equals `bg`
   - Expected: pixels[0] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rounded_rect(4, 4, 8, 6, 2, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[4 * 16 + 4]).to_equal(bg)
        expect(pixels[4 * 16 + 5]).to_equal(bg)
        expect(pixels[4 * 16 + 6]).to_equal(fg)
        expect(pixels[6 * 16 + 4]).to_equal(fg)
        expect(pixels[6 * 16 + 8]).to_equal(fg)
        expect(pixels[9 * 16 + 11]).to_equal(bg)
        expect(pixels[0]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_triangle_filled writes filled pixels through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw triangle filled

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[4 * 16 + 4] equals `fg`
   - Expected: pixels[4 * 16 + 10] equals `fg`
   - Expected: pixels[10 * 16 + 4] equals `fg`
   - Expected: pixels[5 * 16 + 5] equals `fg`
   - Expected: pixels[6 * 16 + 6] equals `fg`
   - Expected: pixels[10 * 16 + 10] equals `bg`
   - Expected: pixels[3 * 16 + 4] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_triangle_filled(4, 4, 10, 4, 4, 10, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[4 * 16 + 4]).to_equal(fg)
        expect(pixels[4 * 16 + 10]).to_equal(fg)
        expect(pixels[10 * 16 + 4]).to_equal(fg)
        expect(pixels[5 * 16 + 5]).to_equal(fg)
        expect(pixels[6 * 16 + 6]).to_equal(fg)
        expect(pixels[10 * 16 + 10]).to_equal(bg)
        expect(pixels[3 * 16 + 4]).to_equal(bg)
        engine.shutdown()
```

</details>

#### clear then draw_rect_filled matches CPU reference pixel-for-pixel

1. var engine = result unwrap

2. engine clear

3. engine draw rect filled

4. engine present
   - Expected: mismatch_count equals `0`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.draw_rect_filled(2, 2, 6, 6, fg)
        engine.present()
        val pixels = engine.read_pixels()
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            val px = ci % 16
            val py = ci / 16
            val expected = if px >= 2 and px < 8 and py >= 2 and py < 8: fg else: bg
            if pixels[ci] != expected:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
        engine.shutdown()
```

</details>

#### draw_image writes uploaded pixels through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw image

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: mismatch_count equals `0`
   - Expected: pixels[0] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val img0 = 0x01020304 as u32
        val img1 = 0x05060708 as u32
        val img2 = 0x11121314 as u32
        val img3 = 0x15161718 as u32
        engine.clear(bg)
        engine.draw_image(5, 6, 2, 2, [img0, img1, img2, img3])
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        var mismatch_count = 0
        if pixels[6 * 16 + 5] != img0:
            mismatch_count = mismatch_count + 1
        if pixels[6 * 16 + 6] != img1:
            mismatch_count = mismatch_count + 1
        if pixels[7 * 16 + 5] != img2:
            mismatch_count = mismatch_count + 1
        if pixels[7 * 16 + 6] != img3:
            mismatch_count = mismatch_count + 1
        expect(mismatch_count).to_equal(0)
        expect(pixels[0]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_gradient_rect writes interpolated rows through the CUDA framebuffer

1. var engine = result unwrap

2. engine clear

3. engine draw gradient rect

4. engine present
   - Expected: pixels.len() equals `256`
   - Expected: mismatch_count equals `0`
   - Expected: pixels[0] equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val top = 0xFF000000 as u32
        val bottom = 0xFF0F1E2D as u32
        engine.clear(bg)
        engine.draw_gradient_rect(3, 4, 5, 4, top, bottom)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        val mid1 = 0xFF050A0F as u32
        val mid2 = 0xFF0A141E as u32
        var mismatch_count = 0
        var row = 0
        while row < 4:
            val expected = if row == 0: top else: if row == 1: mid1 else: if row == 2: mid2 else: bottom
            var col = 0
            while col < 5:
                if pixels[(4 + row) * 16 + 3 + col] != expected:
                    mismatch_count = mismatch_count + 1
                col = col + 1
            row = row + 1
        expect(mismatch_count).to_equal(0)
        expect(pixels[0]).to_equal(bg)
        engine.shutdown()
```

</details>

#### draw_text and clip and mask device readback

#### draw_text result is visible in device readback

1. var engine = result unwrap

2. engine clear

3. engine draw text

4. engine present
   - Expected: cuda_pixels.len() equals `256`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        engine.clear(bg)
        engine.draw_text(0, 0, "X", color_red_u32(), 8)
        engine.present()
        val cuda_pixels = engine.read_pixels()
        expect(cuda_pixels.len()).to_equal(256)
        var non_bg = 0
        var idx = 0
        while idx < 256:
            if cuda_pixels[idx] != bg:
                non_bg = non_bg + 1
            idx = idx + 1
        expect(non_bg).to_be_greater_than(0)
        engine.shutdown()
```

</details>

#### set_clip constrains draw_rect_filled visible via device readback

1. var engine = result unwrap

2. engine clear

3. engine set clip

4. engine draw rect filled

5. engine clear clip

6. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `fg`
   - Expected: pixels[3 * 16 + 3] equals `fg`
   - Expected: pixels[4 * 16 + 4] equals `bg`
   - Expected: pixels[15 * 16 + 15] equals `bg`

7. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.set_clip(0, 0, 4, 4)
        engine.draw_rect_filled(0, 0, 16, 16, fg)
        engine.clear_clip()
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[0]).to_equal(fg)
        expect(pixels[3 * 16 + 3]).to_equal(fg)
        expect(pixels[4 * 16 + 4]).to_equal(bg)
        expect(pixels[15 * 16 + 15]).to_equal(bg)
        engine.shutdown()
```

</details>

#### clear_clip restores full-surface drawing via device readback

1. var engine = result unwrap

2. engine clear

3. engine set clip

4. engine clear clip

5. engine draw rect filled

6. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[15 * 16 + 15] equals `fg`
   - Expected: pixels[0] equals `fg`

7. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        engine.set_clip(0, 0, 2, 2)
        engine.clear_clip()
        engine.draw_rect_filled(0, 0, 16, 16, fg)
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[15 * 16 + 15]).to_equal(fg)
        expect(pixels[0]).to_equal(fg)
        engine.shutdown()
```

</details>

#### set_mask constrains draw_rect_filled visible via device readback

1. var engine = result unwrap

2. engine clear

3. engine set mask

4. engine draw rect filled

5. engine clear mask

6. engine present
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `fg`
   - Expected: pixels[1] equals `bg`
   - Expected: pixels[16] equals `fg`
   - Expected: pixels[17] equals `bg`

7. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val bg = color_blue_u32()
        val fg = color_red_u32()
        engine.clear(bg)
        # mask_buf[i]==0 means blocked; 1 means allowed
        # mask layout [col0_row0, col1_row0, col0_row1, col1_row1]
        # pixel (0,0)=1(pass), (1,0)=0(block), (0,1)=1(pass), (1,1)=0(block)
        engine.set_mask([1u8, 0u8, 1u8, 0u8], 2, 2)
        engine.draw_rect_filled(0, 0, 2, 2, fg)
        engine.clear_mask()
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[0]).to_equal(fg)
        expect(pixels[1]).to_equal(bg)
        expect(pixels[16]).to_equal(fg)
        expect(pixels[17]).to_equal(bg)
        engine.shutdown()
```

</details>

#### sync and readback correctness

#### read_pixels after present reflects latest draw

1. var engine = result unwrap

2. engine clear

3. engine present

4. engine clear

5. engine present
   - Expected: first_pixels[0] equals `first_color`
   - Expected: second_pixels[0] equals `second_color`

6. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
if probe.is_usable():
    val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
    if result.is_ok():
        var engine = result.unwrap()
        val first_color = color_blue_u32()
        val second_color = color_red_u32()
        engine.clear(first_color)
        engine.present()
        val first_pixels = engine.read_pixels()
        engine.clear(second_color)
        engine.present()
        val second_pixels = engine.read_pixels()
        expect(first_pixels[0]).to_equal(first_color)
        expect(second_pixels[0]).to_equal(second_color)
        engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/cuda_strict_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CUDA strict smoke tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
