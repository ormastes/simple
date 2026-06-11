# Compositor Specification

> <details>

<!-- sdn-diagram:id=compositor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compositor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compositor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compositor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Specification

## Scenarios

### EngineColor constructors

#### creates red color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red = EngineColor.red()
expect(red.r).to_equal(1.0)
expect(red.g).to_equal(0.0)
expect(red.b).to_equal(0.0)
expect(red.a).to_equal(1.0)
```

</details>

#### creates from rgb

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.rgb(0.5, 0.25, 0.75)
expect(c.r).to_equal(0.5)
expect(c.g).to_equal(0.25)
expect(c.b).to_equal(0.75)
expect(c.a).to_equal(1.0)
```

</details>

#### creates from rgba

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.rgba(0.1, 0.2, 0.3, 0.4)
expect(c.r).to_equal(0.1)
expect(c.a).to_equal(0.4)
```

</details>

#### creates from hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.from_hex(0xFF0000)
expect(c.r).to_equal(1.0)
expect(c.g).to_equal(0.0)
expect(c.a).to_equal(1.0)
```

</details>

#### creates from hex with alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.from_hex_alpha(0xFF000080)
expect(c.r).to_equal(1.0)
```

</details>

#### has color presets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = EngineColor.white()
expect(w.r).to_equal(1.0)
expect(w.g).to_equal(1.0)
val b = EngineColor.black()
expect(b.r).to_equal(0.0)
val t = EngineColor.transparent()
expect(t.a).to_equal(0.0)
```

</details>

### EngineColor operations

#### modifies alpha with with_alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.red()
val faded = c.with_alpha(0.5)
expect(faded.r).to_equal(1.0)
expect(faded.a).to_equal(0.5)
```

</details>

#### converts to rgba8

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val rgba = white.to_rgba8()
expect(rgba.r).to_equal(255)
expect(rgba.g).to_equal(255)
expect(rgba.b).to_equal(255)
expect(rgba.a).to_equal(255)
```

</details>

#### converts black to rgba8

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val black = EngineColor.black()
val rgba = black.to_rgba8()
expect(rgba.r).to_equal(0)
expect(rgba.g).to_equal(0)
expect(rgba.b).to_equal(0)
expect(rgba.a).to_equal(255)
```

</details>

#### lerps between colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = EngineColor.black()
val b = EngineColor.white()
val mid = a.lerp(b, 0.5)
expect(mid.r).to_be_greater_than(0.4)
expect(mid.r).to_be_less_than(0.6)
```

</details>

#### lerps at extremes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = EngineColor.red()
val b = EngineColor.blue()
val start = a.lerp(b, 0.0)
expect(start.r).to_equal(1.0)
val end_c = a.lerp(b, 1.0)
expect(end_c.b).to_equal(1.0)
```

</details>

#### tests equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = EngineColor.red()
val b = EngineColor.red()
expect(a.eq(b)).to_equal(true)
val c = EngineColor.blue()
expect(a.eq(c)).to_equal(false)
```

</details>

### RGBA packing (rasterizer helper)

#### packs white to expected value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val packed = test_pack_rgba(white)
# white = (255, 255, 255, 255)
# packed = 255*16777216 + 255*65536 + 255*256 + 255 = 4294967295
expect(packed).to_be_greater_than(0)
```

</details>

#### packs red correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red = EngineColor.red()
val packed = test_pack_rgba(red)
# red = (255, 0, 0, 255) -> 255*16777216 + 0 + 0 + 255 = 4278190335
val expected = 255 * 16777216 + 0 + 0 + 255
expect(packed).to_equal(expected)
```

</details>

#### packs black with full alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val black = EngineColor.black()
val packed = test_pack_rgba(black)
# black = (0, 0, 0, 255) -> 0 + 0 + 0 + 255 = 255
expect(packed).to_equal(255)
```

</details>

#### packs transparent to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = EngineColor.transparent()
val packed = test_pack_rgba(t)
expect(packed).to_equal(0)
```

</details>

#### packs green correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val green = EngineColor.green()
val packed = test_pack_rgba(green)
# green = (0, 255, 0, 255) -> 0 + 255*65536 + 0 + 255 = 16711935
val expected = 255 * 65536 + 255
expect(packed).to_equal(expected)
```

</details>

#### packs blue correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blue = EngineColor.blue()
val packed = test_pack_rgba(blue)
# blue = (0, 0, 255, 255) -> 0 + 0 + 255*256 + 255 = 65535
val expected = 255 * 256 + 255
expect(packed).to_equal(expected)
```

</details>

### clamp_byte (rasterizer helper)

#### clamps negative to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_clamp_byte(-10)).to_equal(0)
```

</details>

#### clamps above 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_clamp_byte(300)).to_equal(255)
```

</details>

#### passes through valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_clamp_byte(0)).to_equal(0)
expect(test_clamp_byte(128)).to_equal(128)
expect(test_clamp_byte(255)).to_equal(255)
```

</details>

### EngineColor tinting (rasterizer opacity)

#### applies opacity to color alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = EngineColor.red()
val opacity = 0.5
val tinted = EngineColor(r: color.r, g: color.g, b: color.b, a: color.a * opacity)
expect(tinted.r).to_equal(1.0)
expect(tinted.a).to_equal(0.5)
```

</details>

#### zero opacity produces transparent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = EngineColor.white()
val tinted = EngineColor(r: color.r, g: color.g, b: color.b, a: color.a * 0.0)
expect(tinted.a).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/compositor/compositor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- EngineColor constructors
- EngineColor operations
- RGBA packing (rasterizer helper)
- clamp_byte (rasterizer helper)
- EngineColor tinting (rasterizer opacity)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
