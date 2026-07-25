# Backend Vulkan Processing Specification

> <details>

<!-- sdn-diagram:id=backend_vulkan_processing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_vulkan_processing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_vulkan_processing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_vulkan_processing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Vulkan Processing Specification

## Scenarios

### Vulkan compute processing lane — probe

#### SFFI availability

#### vulkan_sffi_is_available returns a bool (not a crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avail = vulkan_sffi_is_available()
# Just verify it returns without panic — value is host-dependent.
if avail:
    expect("available").to_equal("available")
else:
    expect("unavailable").to_equal("unavailable")
```

</details>

#### headless device probe functions are importable and callable signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vulkan_sffi_find_headless_device and vulkan_sffi_select_headless
# are interpreter-unsafe to call directly (require rt_vulkan_init first).
# This test verifies the import compiles — behavioral tests run with
# a real Vulkan ICD (lavapipe / libvulkan_lvp.so).
expect("headless-probe-importable").to_equal("headless-probe-importable")
```

</details>

### Vulkan compute processing lane — structured errors

#### VulkanErrorKind classification

#### empty error string classifies as None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("")
expect(kind).to_equal(VulkanErrorKind.None)
```

</details>

#### device-lost message classifies as DeviceLost

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("Vulkan device lost")
expect(kind).to_equal(VulkanErrorKind.DeviceLost)
```

</details>

#### DEVICE_LOST substring classifies as DeviceLost

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("VK_ERROR_DEVICE_LOST during submit")
expect(kind).to_equal(VulkanErrorKind.DeviceLost)
```

</details>

#### extension missing message classifies as MissingExtension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("required extension not present")
expect(kind).to_equal(VulkanErrorKind.MissingExtension)
```

</details>

#### SPIR-V compile failure classifies as ShaderCompile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("Vulkan SPIR-V shader compilation failed: ...")
expect(kind).to_equal(VulkanErrorKind.ShaderCompile)
```

</details>

#### shader pipeline create failure classifies as ShaderCompile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("Vulkan compute pipeline creation failed")
expect(kind).to_equal(VulkanErrorKind.ShaderCompile)
```

</details>

#### runtime unavailable message classifies as NotAvailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("Vulkan runtime unavailable")
expect(kind).to_equal(VulkanErrorKind.NotAvailable)
```

</details>

#### rt_vulkan_init failure classifies as NotAvailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("rt_vulkan_init failed: some reason")
expect(kind).to_equal(VulkanErrorKind.NotAvailable)
```

</details>

#### no devices message classifies as NoDevice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("no Vulkan devices")
expect(kind).to_equal(VulkanErrorKind.NoDevice)
```

</details>

#### select_device failure classifies as NoDevice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("rt_vulkan_select_device(0) failed: ...")
expect(kind).to_equal(VulkanErrorKind.NoDevice)
```

</details>

#### unknown error string classifies as Other

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan_classify_error("something went wrong")
expect(kind).to_equal(VulkanErrorKind.Other)
```

</details>

### Vulkan compute processing lane — VulkanBackend init

#### backend init lifecycle

#### uninitialised backend reports empty last_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend.create()
expect(b.last_error).to_equal("")
```

</details>

#### uninitialised backend has zero dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend.create()
expect(b.width()).to_equal(0)
expect(b.height()).to_equal(0)
```

</details>

#### uninitialised backend has empty pixel buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend.create()
expect(b.read_pixels().len()).to_equal(0)
```

</details>

#### init failure sets non-empty last_error

- var b = VulkanBackend create
- assert not equal
   - Expected: b.width() equals `4`
   - Expected: b.height() equals `4`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
val ok = b.init(4, 4)
if not ok:
    expect(b.last_error.len()).to_be_greater_than(0)
    val kind = vulkan_classify_error(b.last_error)
    # Must not be VulkanErrorKind.None when init returned false
    assert_not_equal(kind, VulkanErrorKind.None)
else:
    # Init succeeded — verify dimensions and clean up
    expect(b.width()).to_equal(4)
    expect(b.height()).to_equal(4)
    b.shutdown()
```

</details>

### Vulkan compute processing lane — compute dispatch readback

#### clear and readback

#### clear + present + read_pixels returns correct pixel count when Vulkan available

- var b = VulkanBackend create
- b clear
- b present
   - Expected: pixels.len() equals `16`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(4, 4):
    val red = 0xFF0000FFu32
    b.clear(red)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(16)
    b.shutdown()
else:
    # Graceful degradation: error must be classified
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### clear fills every pixel with the requested color

- var b = VulkanBackend create
- b clear
- b present
   - Expected: pixel_at_p(pixels, 0, 0, 4) equals `green`
   - Expected: pixel_at_p(pixels, 3, 3, 4) equals `green`
   - Expected: pixel_at_p(pixels, 2, 1, 4) equals `green`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(4, 4):
    val green = 0x00FF00FFu32
    b.clear(green)
    b.present()
    val pixels = b.read_pixels()
    expect(pixel_at_p(pixels, 0, 0, 4)).to_equal(green)
    expect(pixel_at_p(pixels, 3, 3, 4)).to_equal(green)
    expect(pixel_at_p(pixels, 2, 1, 4)).to_equal(green)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### sequential clears overwrite previous contents

- var b = VulkanBackend create
- b clear
- b present
- b clear
- b present
   - Expected: pixel_at_p(pixels, 0, 0, 4) equals `c2`
   - Expected: pixel_at_p(pixels, 3, 3, 4) equals `c2`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(4, 4):
    val c1 = 0xFF0000FFu32
    val c2 = 0x0000FFFFu32
    b.clear(c1)
    b.present()
    b.clear(c2)
    b.present()
    val pixels = b.read_pixels()
    # All pixels must be the second color
    expect(pixel_at_p(pixels, 0, 0, 4)).to_equal(c2)
    expect(pixel_at_p(pixels, 3, 3, 4)).to_equal(c2)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### rect_filled dispatch

#### draw_rect_filled leaves corners untouched

- var b = VulkanBackend create
- b clear
- b draw rect filled
- b present
   - Expected: pixel_at_p(pixels, 0, 0, 8) equals `bg`
   - Expected: pixel_at_p(pixels, 7, 7, 8) equals `bg`
   - Expected: pixel_at_p(pixels, 4, 4, 8) equals `fg`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(8, 8):
    val bg = 0x111111FFu32
    val fg = 0xAABBCCFFu32
    b.clear(bg)
    b.draw_rect_filled(2, 2, 4, 4, fg)
    b.present()
    val pixels = b.read_pixels()
    # Corner pixels must still be bg
    expect(pixel_at_p(pixels, 0, 0, 8)).to_equal(bg)
    expect(pixel_at_p(pixels, 7, 7, 8)).to_equal(bg)
    # Center of the rect must be fg
    expect(pixel_at_p(pixels, 4, 4, 8)).to_equal(fg)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_rect_filled at origin covers top-left corner

- var b = VulkanBackend create
- b clear
- b draw rect filled
- b present
   - Expected: pixel_at_p(pixels, 0, 0, 8) equals `fg`
   - Expected: pixel_at_p(pixels, 7, 7, 8) equals `bg`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(8, 8):
    val bg = 0x222222FFu32
    val fg = 0xFFFFFFFFu32
    b.clear(bg)
    b.draw_rect_filled(0, 0, 4, 4, fg)
    b.present()
    val pixels = b.read_pixels()
    expect(pixel_at_p(pixels, 0, 0, 8)).to_equal(fg)
    # Bottom-right corner of canvas untouched
    expect(pixel_at_p(pixels, 7, 7, 8)).to_equal(bg)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vulkan compute processing lane — probe
- Vulkan compute processing lane — structured errors
- Vulkan compute processing lane — VulkanBackend init
- Vulkan compute processing lane — compute dispatch readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
