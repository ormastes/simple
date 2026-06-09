# Metal Engine2d Readback Specification

> <details>

<!-- sdn-diagram:id=metal_engine2d_readback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metal_engine2d_readback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metal_engine2d_readback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metal_engine2d_readback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Engine2d Readback Specification

## Scenarios

### Metal Engine2D framebuffer readback

#### raw GPU pixels

#### downloads clear and rect_filled pixels from the Metal framebuffer

- var b = MetalBackend create
   - Expected: b.init(16, 16) is true
- b clear
- b draw rect filled
   - Expected: b.gpu_frame_complete is true
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `0x10203040 as u32`
   - Expected: pixels[4 + (4 * 16)] equals `0x01020304 as u32`
- b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0x10203040 as u32)
    b.draw_rect_filled(4, 4, 4, 4, 0x01020304 as u32)
    expect(b.gpu_frame_complete).to_equal(true)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)
    expect(pixels[0]).to_equal(0x10203040 as u32)
    expect(pixels[4 + (4 * 16)]).to_equal(0x01020304 as u32)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_rect pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw rect
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rect
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_rect(4, 4, 6, 6, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_rect(4, 4, 6, 6, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_rect_filled pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw rect filled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rect filled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_rect_filled(4, 4, 4, 4, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_rect_filled(4, 4, 4, 4, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_circle pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw circle
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw circle
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_circle(8, 8, 4, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_circle(8, 8, 4, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_rounded_rect pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw rounded rect
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rounded rect
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_rounded_rect(2, 3, 10, 8, 2, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_rounded_rect(2, 3, 10, 8, 2, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_gradient_rect pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw gradient rect
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw gradient rect
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_gradient_rect(4, 2, 7, 10, 0xffff0000u32, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_gradient_rect(4, 2, 7, 10, 0xffff0000u32, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_triangle_filled pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw triangle filled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw triangle filled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_triangle_filled(8, 2, 3, 11, 12, 13, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_triangle_filled(8, 2, 3, 11, 12, 13, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_line pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw line
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw line
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_line(0, 12, 23, 12, 0xff00ff00u32, 1)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_line(0, 12, 23, 12, 0xff00ff00u32, 1)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_circle_filled pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw circle filled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw circle filled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_circle_filled(16, 8, 4, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_circle_filled(16, 8, 4, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### falls back after CPU-only text rendering invalidates GPU completeness

- var b = MetalBackend create
   - Expected: b.init(16, 16) is true
- b clear
- b draw text
   - Expected: b.gpu_frame_complete is false
   - Expected: pixels.len() equals `256`
- b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0x10203040 as u32)
    b.draw_text(1, 1, "A", 0x01020304 as u32, 8)
    expect(b.gpu_frame_complete).to_equal(false)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads draw_image and draw_image_scaled pixels from the Metal framebuffer

- var b = MetalBackend create
   - Expected: b.init(16, 16) is true
- b clear
- b draw image
   - Expected: b.gpu_frame_complete is true
- var pixels = b read pixels
   - Expected: pixels[5 + (6 * 16)] equals `0xff0000ffu32`
   - Expected: pixels[6 + (6 * 16)] equals `0xff00ff00u32`
   - Expected: pixels[5 + (7 * 16)] equals `0xffff0000u32`
   - Expected: pixels[6 + (7 * 16)] equals `0xffffffffu32`
- b clear
- b draw image scaled
   - Expected: b.gpu_frame_complete is true
- pixels = b read pixels
   - Expected: pixels[2 + (3 * 16)] equals `0xff0000ffu32`
   - Expected: pixels[5 + (3 * 16)] equals `0xff00ff00u32`
   - Expected: pixels[2 + (6 * 16)] equals `0xffff0000u32`
   - Expected: pixels[5 + (6 * 16)] equals `0xffffffffu32`
- b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0x00112233 as u32)
    val src = [
        0xff0000ffu32, 0xff00ff00u32,
        0xffff0000u32, 0xffffffffu32
    ]
    b.draw_image(5, 6, 2, 2, src)
    expect(b.gpu_frame_complete).to_equal(true)
    var pixels = b.read_pixels()
    expect(pixels[5 + (6 * 16)]).to_equal(0xff0000ffu32)
    expect(pixels[6 + (6 * 16)]).to_equal(0xff00ff00u32)
    expect(pixels[5 + (7 * 16)]).to_equal(0xffff0000u32)
    expect(pixels[6 + (7 * 16)]).to_equal(0xffffffffu32)

    b.clear(0x00112233 as u32)
    b.draw_image_scaled(2, 3, 4, 4, 2, 2, src)
    expect(b.gpu_frame_complete).to_equal(true)
    pixels = b.read_pixels()
    expect(pixels[2 + (3 * 16)]).to_equal(0xff0000ffu32)
    expect(pixels[5 + (3 * 16)]).to_equal(0xff00ff00u32)
    expect(pixels[2 + (6 * 16)]).to_equal(0xffff0000u32)
    expect(pixels[5 + (6 * 16)]).to_equal(0xffffffffu32)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_image_transform

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw image transform
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw image transform
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    val src = [
        0xffff0000u32, 0xff00ff00u32,
        0xff0000ffu32, 0xffffffffu32
    ]
    strict.clear(0xff000000u32)
    strict.draw_image_transform(10, 4, 2, 2, 256, 64, 0, 256, 0, 0, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_image_transform(10, 4, 2, 2, 256, 64, 0, 256, 0, 0, src)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_image

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw image
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw image
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    val src = [
        0xff0000ffu32, 0xff00ff00u32,
        0xffff0000u32, 0xffffffffu32
    ]
    strict.clear(0x00112233 as u32)
    strict.draw_image(5, 6, 2, 2, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0x00112233 as u32)
    ref.draw_image(5, 6, 2, 2, src)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_image_scaled

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw image scaled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw image scaled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    val src = [
        0xff0000ffu32, 0xff00ff00u32,
        0xffff0000u32, 0xffffffffu32
    ]
    strict.clear(0x00112233 as u32)
    strict.draw_image_scaled(2, 3, 4, 4, 2, 2, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0x00112233 as u32)
    ref.draw_image_scaled(2, 3, 4, 4, 2, 2, src)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_blur_rect

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw rect filled
- strict draw blur rect
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rect filled
- ref draw blur rect
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_rect_filled(6, 6, 8, 6, 0xffff0000u32)
    strict.draw_blur_rect(6, 6, 8, 6, 2)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_rect_filled(6, 6, 8, 6, 0xffff0000u32)
    ref.draw_blur_rect(6, 6, 8, 6, 2)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_shadow_rect

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw shadow rect
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw shadow rect
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_shadow_rect(12, 3, 4, 3, 1, 1, 1, 0x80000000u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_shadow_rect(12, 3, 4, 3, 1, 1, 1, 0x80000000u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available after software-replay advanced ops

- var b = MetalBackend create
   - Expected: b.init(16, 16) is true
- b clear
- b draw gradient rect h
   - Expected: b.gpu_frame_complete is true
- var pixels = b read pixels
   - Expected: pixels[2 + (4 * 16)] equals `0xffff0000u32`
   - Expected: pixels[7 + (4 * 16)] equals `0xff00ff00u32`
- b clear
- b draw rect blend
   - Expected: b.gpu_frame_complete is true
- pixels = b read pixels
   - Expected: pixels[1 + (1 * 16)] equals `0xff800000u32`
- b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0xff000000u32)
    b.draw_gradient_rect_h(2, 4, 6, 2, 0xffff0000u32, 0xff00ff00u32)
    expect(b.gpu_frame_complete).to_equal(true)
    var pixels = b.read_pixels()
    expect(pixels[2 + (4 * 16)]).to_equal(0xffff0000u32)
    expect(pixels[7 + (4 * 16)]).to_equal(0xff00ff00u32)

    b.clear(0xff000000u32)
    b.draw_rect_blend(1, 1, 3, 3, 0x80ff0000u32)
    expect(b.gpu_frame_complete).to_equal(true)
    pixels = b.read_pixels()
    expect(pixels[1 + (1 * 16)]).to_equal(0xff800000u32)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_rect_blend

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw rect blend
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rect blend
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff204060u32)
    strict.draw_rect_blend(1, 1, 3, 3, 0x80ff0000u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff204060u32)
    ref.draw_rect_blend(1, 1, 3, 3, 0x80ff0000u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_image_blend

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw image blend
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw image blend
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    val src = [
        0xffff0000u32, 0xff00ff00u32,
        0xff0000ffu32, 0xffffffffu32
    ]
    strict.clear(0xff204060u32)
    strict.draw_image_blend(3, 4, 2, 2, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff204060u32)
    ref.draw_image_blend(3, 4, 2, 2, src)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_rect_blend_mode

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw rect blend mode
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rect blend mode
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff204060u32)
    strict.draw_rect_blend_mode(2, 2, 3, 3, 0x80ff0000u32, 1)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff204060u32)
    ref.draw_rect_blend_mode(2, 2, 3, 3, 0x80ff0000u32, 1)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_gradient_rect_h

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw gradient rect h
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw gradient rect h
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_gradient_rect_h(0, 4, 8, 1, 0xffff0000u32, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_gradient_rect_h(0, 4, 8, 1, 0xffff0000u32, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_radial_gradient

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw radial gradient
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw radial gradient
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_radial_gradient(8, 8, 4, 0xffffffffu32, 0xff0000ffu32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_radial_gradient(8, 8, 4, 0xffffffffu32, 0xff0000ffu32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads native draw_ellipse_filled pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw ellipse filled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw ellipse filled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_ellipse_filled(8, 8, 4, 2, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_ellipse_filled(8, 8, 4, 2, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_ellipse pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw ellipse
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw ellipse
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_ellipse(8, 8, 4, 2, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_ellipse(8, 8, 4, 2, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_arc

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw arc
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw arc
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_arc(12, 12, 6, 30, 160, 0xff00ff00u32, 2)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_arc(12, 12, 6, 30, 160, 0xff00ff00u32, 2)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_bezier

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw bezier
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw bezier
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_bezier(2, 18, 6, 2, 18, 4, 21, 18, 0xff00ff00u32, 1)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_bezier(2, 18, 6, 2, 18, 4, 21, 18, 0xff00ff00u32, 1)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_polygon_filled

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw polygon filled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw polygon filled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    val xs = [4, 12, 19, 15, 7]
    val ys = [18, 4, 8, 19, 16]
    strict.clear(0xff000000u32)
    strict.draw_polygon_filled(xs, ys, 5, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_polygon_filled(xs, ys, 5, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_polyline

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw polyline
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw polyline
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    val xs = [2, 8, 14, 20]
    val ys = [18, 6, 16, 8]
    strict.clear(0xff000000u32)
    strict.draw_polyline(xs, ys, 4, 0xff00ff00u32, 1)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_polyline(xs, ys, 4, 0xff00ff00u32, 1)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### keeps GPU readback available for draw_triangle_outline

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw triangle outline
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw triangle outline
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_triangle_outline(8, 2, 3, 11, 12, 13, 0xff00ff00u32, 1)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_triangle_outline(8, 2, 3, 11, 12, 13, 0xff00ff00u32, 1)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_circle_thick pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(20, 20) is true
- strict clear
- strict draw circle thick
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw circle thick
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(20, 20)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_circle_thick(10, 10, 5, 0xff00ff00u32, 2)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(20, 20, "software")
    ref.clear(0xff000000u32)
    ref.draw_circle_thick(10, 10, 5, 0xff00ff00u32, 2)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### downloads direct draw_rounded_rect_outline pixels from the Metal framebuffer

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(24, 24) is true
- strict clear
- strict draw rounded rect outline
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref draw rounded rect outline
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(24, 24)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_rounded_rect_outline(4, 5, 12, 10, 3, 0xff00ff00u32, 2)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(24, 24, "software")
    ref.clear(0xff000000u32)
    ref.draw_rounded_rect_outline(4, 5, 12, 10, 3, 0xff00ff00u32, 2)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict mode keeps GPU readback available for draw_text and draw_text_bg

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw text
   - Expected: strict.gpu_frame_complete is true
   - Expected: strict_text_pixels.len() equals `256`
- var ref text = Engine2D create with backend
- ref text clear
- ref text draw text
- ref text present
- ref text shutdown
   - Expected: count_pixel_mismatches(strict_text_pixels, ref_text_pixels) equals `0`
- strict clear
- strict draw text bg
   - Expected: strict.gpu_frame_complete is true
   - Expected: strict_text_bg_pixels.len() equals `256`
- var ref text bg = Engine2D create with backend
- ref text bg clear
- ref text bg draw text bg
- ref text bg present
- ref text bg shutdown
   - Expected: count_pixel_mismatches(strict_text_bg_pixels, ref_text_bg_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_text(1, 1, "A", 0xffffffffu32, 8)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_text_pixels = strict.read_pixels()
    expect(strict_text_pixels.len()).to_equal(256)

    var ref_text = Engine2D.create_with_backend(16, 16, "software")
    ref_text.clear(0xff000000u32)
    ref_text.draw_text(1, 1, "A", 0xffffffffu32, 8)
    ref_text.present()
    val ref_text_pixels = ref_text.read_pixels()
    ref_text.shutdown()
    expect(count_pixel_mismatches(strict_text_pixels, ref_text_pixels)).to_equal(0)

    strict.clear(0xff000000u32)
    strict.draw_text_bg(2, 2, "A", 0xffffffffu32, 0xff004400u32, 8)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_text_bg_pixels = strict.read_pixels()
    expect(strict_text_bg_pixels.len()).to_equal(256)

    var ref_text_bg = Engine2D.create_with_backend(16, 16, "software")
    ref_text_bg.clear(0xff000000u32)
    ref_text_bg.draw_text_bg(2, 2, "A", 0xffffffffu32, 0xff004400u32, 8)
    ref_text_bg.present()
    val ref_text_bg_pixels = ref_text_bg.read_pixels()
    ref_text_bg.shutdown()
    expect(count_pixel_mismatches(strict_text_bg_pixels, ref_text_bg_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict mode keeps GPU readback available for draw_text

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw text
   - Expected: strict.gpu_frame_complete is true
   - Expected: strict_pixels.len() equals `256`
- var ref = Engine2D create with backend
- ref clear
- ref draw text
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_text(1, 1, "A", 0xffffffffu32, 8)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()
    expect(strict_pixels.len()).to_equal(256)

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_text(1, 1, "A", 0xffffffffu32, 8)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict mode keeps GPU readback available for draw_text_bg

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict draw text bg
   - Expected: strict.gpu_frame_complete is true
   - Expected: strict_pixels.len() equals `256`
- var ref = Engine2D create with backend
- ref clear
- ref draw text bg
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.draw_text_bg(2, 2, "A", 0xffffffffu32, 0xff004400u32, 8)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()
    expect(strict_pixels.len()).to_equal(256)

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_text_bg(2, 2, "A", 0xffffffffu32, 0xff004400u32, 8)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()

    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict state-only clip changes preserve readback and replayed ops honor clip

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
   - Expected: strict.gpu_frame_complete is true
- strict set clip
   - Expected: strict.gpu_frame_complete is true
   - Expected: clipped_clear.len() equals `256`
   - Expected: clipped_clear[0] equals `0xff000000u32`
- strict draw gradient rect h
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref set clip
- ref draw gradient rect h
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    strict.set_clip(4, 4, 4, 4)
    expect(strict.gpu_frame_complete).to_equal(true)
    val clipped_clear = strict.read_pixels()
    expect(clipped_clear.len()).to_equal(256)
    expect(clipped_clear[0]).to_equal(0xff000000u32)

    strict.draw_gradient_rect_h(0, 4, 8, 1, 0xffff0000u32, 0xff00ff00u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.set_clip(4, 4, 4, 4)
    ref.draw_gradient_rect_h(0, 4, 8, 1, 0xffff0000u32, 0xff00ff00u32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict draw_image honors mask via replay when stateful

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict set mask
- strict draw image
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref set mask
- ref draw image
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    val mask = [
        0u8, 0u8, 0u8, 0u8,
        0u8, 1u8, 1u8, 0u8,
        0u8, 1u8, 1u8, 0u8,
        0u8, 0u8, 0u8, 0u8
    ]
    val src = [
        0xffff0000u32, 0xff00ff00u32,
        0xff0000ffu32, 0xffffffffu32
    ]
    strict.clear(0xff000000u32)
    strict.set_mask(mask, 4, 4)
    strict.draw_image(1, 1, 2, 2, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.set_mask(mask, 4, 4)
    ref.draw_image(1, 1, 2, 2, src)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict draw_rect_filled honors mask via replay when stateful

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict set mask
- strict draw rect filled
   - Expected: strict.gpu_frame_complete is true
- var ref = Engine2D create with backend
- ref clear
- ref set mask
- ref draw rect filled
- ref present
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    val mask = [
        0u8, 0u8, 0u8, 0u8,
        0u8, 1u8, 1u8, 0u8,
        0u8, 1u8, 1u8, 0u8,
        0u8, 0u8, 0u8, 0u8
    ]
    strict.clear(0xff000000u32)
    strict.set_mask(mask, 4, 4)
    strict.draw_rect_filled(1, 1, 4, 4, 0xff3366ccu32)
    expect(strict.gpu_frame_complete).to_equal(true)
    val strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.set_mask(mask, 4, 4)
    ref.draw_rect_filled(1, 1, 4, 4, 0xff3366ccu32)
    ref.present()
    val ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### strict direct primitives honor clip and mask via replay when stateful

- var strict = MetalBackend create strict gpu only
   - Expected: strict.init(16, 16) is true
- strict clear
- strict set clip
- strict draw rect filled
   - Expected: strict.gpu_frame_complete is true
- var strict pixels = strict read pixels
- var ref = Engine2D create with backend
- ref clear
- ref set clip
- ref draw rect filled
- ref present
- var ref pixels = ref read pixels
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict clear clip
- strict clear
- strict set mask
- strict draw image
   - Expected: strict.gpu_frame_complete is true
- strict pixels = strict read pixels
- ref = Engine2D create with backend
- ref clear
- ref set mask
- ref draw image
- ref present
- ref pixels = ref read pixels
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict clear mask
- strict clear
- strict draw image blend
   - Expected: strict.gpu_frame_complete is true
- strict pixels = strict read pixels
- ref = Engine2D create with backend
- ref clear
- ref draw image blend
- ref present
- ref pixels = ref read pixels
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict clear
- strict draw rect blend mode
   - Expected: strict.gpu_frame_complete is true
- strict pixels = strict read pixels
- ref = Engine2D create with backend
- ref clear
- ref draw rect blend mode
- ref present
- ref pixels = ref read pixels
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict clear
- strict draw rect blend mode
   - Expected: strict.gpu_frame_complete is true
- strict pixels = strict read pixels
- ref = Engine2D create with backend
- ref clear
- ref draw rect blend mode
- ref present
- ref pixels = ref read pixels
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict clear
- strict draw radial gradient
   - Expected: strict.gpu_frame_complete is true
- strict pixels = strict read pixels
- ref = Engine2D create with backend
- ref clear
- ref draw radial gradient
- ref present
- ref pixels = ref read pixels
- ref shutdown
   - Expected: count_pixel_mismatches(strict_pixels, ref_pixels) equals `0`
- strict shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 99 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var strict = MetalBackend.create_strict_gpu_only()
    expect(strict.init(16, 16)).to_equal(true)
    strict.clear(0xff000000u32)
    strict.set_clip(4, 4, 4, 4)
    strict.draw_rect_filled(2, 4, 8, 2, 0xffff0000u32)
    expect(strict.gpu_frame_complete).to_equal(true)
    var strict_pixels = strict.read_pixels()

    var ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.set_clip(4, 4, 4, 4)
    ref.draw_rect_filled(2, 4, 8, 2, 0xffff0000u32)
    ref.present()
    var ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)

    strict.clear_clip()
    val mask = [
        0u8, 0u8, 0u8, 0u8,
        0u8, 1u8, 1u8, 0u8,
        0u8, 1u8, 1u8, 0u8,
        0u8, 0u8, 0u8, 0u8
    ]
    val src = [
        0xffff0000u32, 0xff00ff00u32,
        0xff0000ffu32, 0xffffffffu32
    ]
    strict.clear(0xff000000u32)
    strict.set_mask(mask, 4, 4)
    strict.draw_image(1, 1, 2, 2, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    strict_pixels = strict.read_pixels()

    ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.set_mask(mask, 4, 4)
    ref.draw_image(1, 1, 2, 2, src)
    ref.present()
    ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)

    strict.clear_mask()
    strict.clear(0xff204060u32)
    strict.draw_image_blend(3, 4, 2, 2, src)
    expect(strict.gpu_frame_complete).to_equal(true)
    strict_pixels = strict.read_pixels()

    ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff204060u32)
    ref.draw_image_blend(3, 4, 2, 2, src)
    ref.present()
    ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)

    strict.clear(0xff204060u32)
    strict.draw_rect_blend_mode(2, 2, 3, 3, 0x80ff0000u32, 0)
    expect(strict.gpu_frame_complete).to_equal(true)
    strict_pixels = strict.read_pixels()

    ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff204060u32)
    ref.draw_rect_blend_mode(2, 2, 3, 3, 0x80ff0000u32, 0)
    ref.present()
    ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)

    strict.clear(0xff204060u32)
    strict.draw_rect_blend_mode(2, 2, 3, 3, 0x80ff0000u32, 1)
    expect(strict.gpu_frame_complete).to_equal(true)
    strict_pixels = strict.read_pixels()

    ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff204060u32)
    ref.draw_rect_blend_mode(2, 2, 3, 3, 0x80ff0000u32, 1)
    ref.present()
    ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)

    strict.clear(0xff000000u32)
    strict.draw_radial_gradient(8, 8, 4, 0xffffffffu32, 0xff0000ffu32)
    expect(strict.gpu_frame_complete).to_equal(true)
    strict_pixels = strict.read_pixels()

    ref = Engine2D.create_with_backend(16, 16, "software")
    ref.clear(0xff000000u32)
    ref.draw_radial_gradient(8, 8, 4, 0xffffffffu32, 0xff0000ffu32)
    ref.present()
    ref_pixels = ref.read_pixels()
    ref.shutdown()
    expect(count_pixel_mismatches(strict_pixels, ref_pixels)).to_equal(0)
    strict.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/metal_engine2d_readback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal Engine2D framebuffer readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
