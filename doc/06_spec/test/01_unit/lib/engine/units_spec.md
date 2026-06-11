# Units Specification

> <details>

<!-- sdn-diagram:id=units_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=units_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

units_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=units_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Units Specification

## Scenarios

### Engine Units

### Seconds

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Seconds(value: 1.5)
expect(s.value).to_equal(1.5)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Seconds(value: 2.0)
expect(s.to_f64()).to_equal(2.0)
```

</details>

#### adds two Seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Seconds(value: 1.0)
val b = Seconds(value: 2.5)
val result = a.add(b)
expect(result.value).to_equal(3.5)
```

</details>

#### subtracts two Seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Seconds(value: 5.0)
val b = Seconds(value: 1.5)
val result = a.sub(b)
expect(result.value).to_equal(3.5)
```

</details>

### Angle

#### creates with radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Angle(radians: 3.14)
expect(a.radians).to_equal(3.14)
```

</details>

#### converts to radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Angle(radians: 1.0)
expect(a.to_radians()).to_equal(1.0)
```

</details>

#### converts to degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Angle(radians: 1.0)
val deg = a.to_degrees()
expect(deg).to_be_greater_than(57.0)
expect(deg).to_be_less_than(58.0)
```

</details>

#### adds two Angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Angle(radians: 1.0)
val b = Angle(radians: 2.0)
val result = a.add(b)
expect(result.radians).to_equal(3.0)
```

</details>

#### creates zero angle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Angle.zero()
expect(a.radians).to_equal(0.0)
```

</details>

### Volume

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Volume(value: 0.8)
expect(v.value).to_equal(0.8)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Volume(value: 0.5)
expect(v.to_f64()).to_equal(0.5)
```

</details>

#### creates full volume

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Volume.full()
expect(v.value).to_equal(1.0)
```

</details>

#### creates muted volume

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Volume.mute_vol()
expect(v.value).to_equal(0.0)
```

</details>

### ZIndex

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = ZIndex(value: 5)
expect(z.value).to_equal(5)
```

</details>

#### converts to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = ZIndex(value: 10)
expect(z.to_i64()).to_equal(10)
```

</details>

#### creates zero ZIndex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = ZIndex.zero()
expect(z.value).to_equal(0)
```

</details>

### KeyCode

#### creates with code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = KeyCode(code: 65)
expect(k.code).to_equal(65)
```

</details>

#### converts to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = KeyCode(code: 32)
expect(k.to_i64()).to_equal(32)
```

</details>

#### compares equal KeyCodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = KeyCode(code: 65)
val b = KeyCode(code: 65)
expect(a.eq(b)).to_equal(true)
```

</details>

#### compares different KeyCodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = KeyCode(code: 65)
val b = KeyCode(code: 66)
expect(a.eq(b)).to_equal(false)
```

</details>

### MouseButtonId

#### creates with code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MouseButtonId(code: 0)
expect(m.code).to_equal(0)
```

</details>

#### converts to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MouseButtonId(code: 1)
expect(m.to_i64()).to_equal(1)
```

</details>

### GamepadButtonId

#### creates with code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = GamepadButtonId(code: 1)
expect(g.code).to_equal(1)
```

</details>

### Distance

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Distance(value: 100.0)
expect(d.value).to_equal(100.0)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Distance(value: 42.5)
expect(d.to_f64()).to_equal(42.5)
```

</details>

### ZoomLevel

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = ZoomLevel(value: 2.0)
expect(z.value).to_equal(2.0)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = ZoomLevel(value: 1.5)
expect(z.to_f64()).to_equal(1.5)
```

</details>

<details>
<summary>Advanced: creates default zoom</summary>

#### creates default zoom

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = ZoomLevel.default_zoom()
expect(z.value).to_equal(1.0)
```

</details>


</details>

### TileCoord

#### creates with col and row

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TileCoord(col: 3, row: 7)
expect(t.col).to_equal(3)
expect(t.row).to_equal(7)
```

</details>

### PixelSize

#### creates with width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PixelSize(width: 1920, height: 1080)
expect(p.width).to_equal(1920)
expect(p.height).to_equal(1080)
```

</details>

### TileIndex

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TileIndex(value: 42)
expect(t.value).to_equal(42)
```

</details>

#### converts to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TileIndex(value: 7)
expect(t.to_i64()).to_equal(7)
```

</details>

#### creates empty TileIndex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TileIndex.empty()
expect(t.value).to_equal(-1)
```

</details>

### FrameIndex

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FrameIndex(value: 10)
expect(f.value).to_equal(10)
```

</details>

#### converts to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FrameIndex(value: 99)
expect(f.to_i64()).to_equal(99)
```

</details>

### Speed

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Speed(value: 5.5)
expect(s.value).to_equal(5.5)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Speed(value: 3.0)
expect(s.to_f64()).to_equal(3.0)
```

</details>

### Tolerance

#### creates with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Tolerance(value: 0.001)
expect(t.value).to_equal(0.001)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Tolerance(value: 0.01)
expect(t.to_f64()).to_equal(0.01)
```

</details>

### RGBA8

#### creates with components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = RGBA8(r: 255, g: 128, b: 0, a: 255)
expect(c.r).to_equal(255)
expect(c.g).to_equal(128)
expect(c.b).to_equal(0)
expect(c.a).to_equal(255)
```

</details>

#### creates black color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = RGBA8(r: 0, g: 0, b: 0, a: 255)
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
expect(c.a).to_equal(255)
```

</details>

#### creates transparent color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = RGBA8(r: 0, g: 0, b: 0, a: 0)
expect(c.a).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/units_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine Units
- Seconds
- Angle
- Volume
- ZIndex
- KeyCode
- MouseButtonId
- GamepadButtonId
- Distance
- ZoomLevel
- TileCoord
- PixelSize
- TileIndex
- FrameIndex
- Speed
- Tolerance
- RGBA8

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
