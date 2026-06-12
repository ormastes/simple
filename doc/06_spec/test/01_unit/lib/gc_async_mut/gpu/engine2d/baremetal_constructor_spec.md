# Baremetal Constructor Specification

> <details>

<!-- sdn-diagram:id=baremetal_constructor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_constructor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_constructor_spec -> std
baremetal_constructor_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_constructor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Constructor Specification

## Scenarios

### Engine2D baremetal constructor

#### preserves explicit dimensions on the sized baremetal path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(8, 6)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend_dims(8, 6, backend)

expect(engine.backend_name()).to_equal("baremetal")
expect(engine.width()).to_equal(8)
expect(engine.height()).to_equal(6)
```

</details>

#### keeps the legacy baremetal constructor contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(11, 7)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend(backend)

expect(engine.backend_name()).to_equal("baremetal")
expect(engine.width()).to_equal(11)
expect(engine.height()).to_equal(7)
```

</details>

#### reads host-backed framebuffer pixels in row-major order

- engine clear
- engine draw rect filled
   - Expected: pixels.len() equals `12`
   - Expected: pixels[0] equals `0xFF010203u32`
   - Expected: pixels[5] equals `0xFFABCDEFu32`
   - Expected: pixels[6] equals `0xFFABCDEFu32`
   - Expected: pixels[11] equals `0xFF010203u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(4, 3)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend_dims(4, 3, backend)
engine.clear(0xFF010203u32)
engine.draw_rect_filled(1, 1, 2, 1, 0xFFABCDEFu32)
val pixels = engine.read_pixels()

expect(pixels.len()).to_equal(12)
expect(pixels[0]).to_equal(0xFF010203u32)
expect(pixels[5]).to_equal(0xFFABCDEFu32)
expect(pixels[6]).to_equal(0xFFABCDEFu32)
expect(pixels[11]).to_equal(0xFF010203u32)
```

</details>

#### draw_text_bg preserves filled background and foreground glyph pixels

- engine clear
- engine draw text bg
   - Expected: pixels[1 * 8 + 1] equals `0xFF112233u32`
   - Expected: pixels[1 * 8 + 3] equals `0xFFFFFFFFu32`
   - Expected: pixels[4 * 8 + 1] equals `0xFFFFFFFFu32`
   - Expected: pixels[7 * 8 + 6] equals `0xFF112233u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(8, 8)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend_dims(8, 8, backend)
engine.clear(0xFF000000u32)
engine.draw_text_bg(1, 1, "A", 0xFFFFFFFFu32, 0xFF112233u32, 7)
val pixels = engine.read_pixels()

expect(pixels[1 * 8 + 1]).to_equal(0xFF112233u32)
expect(pixels[1 * 8 + 3]).to_equal(0xFFFFFFFFu32)
expect(pixels[4 * 8 + 1]).to_equal(0xFFFFFFFFu32)
expect(pixels[7 * 8 + 6]).to_equal(0xFF112233u32)
```

</details>

#### draw_text writes foreground glyph pixels without filling background

- engine clear
- engine draw text
   - Expected: pixels[1 * 8 + 1] equals `0xFF000000u32`
   - Expected: pixels[1 * 8 + 3] equals `0xFFFFFFFFu32`
   - Expected: pixels[4 * 8 + 1] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fb = FramebufferDriver.from_buffer(8, 8)
val backend = BaremetalBackend.create(fb)

val engine = Engine2D.create_with_baremetal_backend_dims(8, 8, backend)
engine.clear(0xFF000000u32)
engine.draw_text(1, 1, "A", 0xFFFFFFFFu32, 7)
val pixels = engine.read_pixels()

expect(pixels[1 * 8 + 1]).to_equal(0xFF000000u32)
expect(pixels[1 * 8 + 3]).to_equal(0xFFFFFFFFu32)
expect(pixels[4 * 8 + 1]).to_equal(0xFFFFFFFFu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D baremetal constructor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
