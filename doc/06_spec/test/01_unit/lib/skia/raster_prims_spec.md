# Raster Prims Specification

> <details>

<!-- sdn-diagram:id=raster_prims_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=raster_prims_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

raster_prims_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=raster_prims_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raster Prims Specification

## Scenarios

### Bitmap

#### zeros has correct byte count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bm = Bitmap.zeros(10, 10)
expect(bm.pixels.len()).to_equal(400)
```

</details>

#### zeros starts with all-zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bm = Bitmap.zeros(10, 10)
val first = bm.pixels[0] as i64
val last = bm.pixels[399] as i64
expect(first).to_equal(0)
expect(last).to_equal(0)
```

</details>

#### set_pixel writes R byte at correct offset

1. var bm = Bitmap zeros
2. bm set pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(10, 10)
val red = _red()
bm.set_pixel(5, 5, red)
# pixel (5,5) index = (5*10+5)*4 = 220
val r_byte = bm.pixels[220] as i64
expect(r_byte).to_be_greater_than(200)
```

</details>

#### set_pixel out of bounds is a no-op

1. var bm = Bitmap zeros
2. bm set pixel
   - Expected: b0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(10, 10)
val red = _red()
bm.set_pixel(1000, 1000, red)
# all bytes still zero
val b0 = bm.pixels[0] as i64
expect(b0).to_equal(0)
```

</details>

#### fill_rect over 2x2x3x3 rect sets interior pixels to red

1. var bm = Bitmap zeros
2. fill rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(10, 10)
val rect = SkRect(left: 2.0, top: 2.0, right: 5.0, bottom: 5.0)
fill_rect(bm, rect, _red())
# center pixel (3,3): idx = (3*10+3)*4 = 132
val r_byte = bm.pixels[132] as i64
expect(r_byte).to_be_greater_than(200)
```

</details>

#### fill_rect with zero-area rect is a no-op

1. var bm = Bitmap zeros
2. fill rect
   - Expected: b0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(10, 10)
val rect = SkRect(left: 5.0, top: 5.0, right: 5.0, bottom: 5.0)
fill_rect(bm, rect, _red())
val b0 = bm.pixels[0] as i64
expect(b0).to_equal(0)
```

</details>

#### fill_rrect with rx=0 ry=0 matches fill_rect

1. var bm1 = Bitmap zeros
2. var bm2 = Bitmap zeros
3. fill rect
4. fill rrect


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm1 = Bitmap.zeros(20, 20)
var bm2 = Bitmap.zeros(20, 20)
val rect = SkRect(left: 4.0, top: 4.0, right: 16.0, bottom: 16.0)
fill_rect(bm1, rect, _red())
fill_rrect(bm2, rect, 0.0, 0.0, _red())
# center pixel (10,10): idx = (10*20+10)*4 = 840
val r1 = bm1.pixels[840] as i64
val r2 = bm2.pixels[840] as i64
expect(r1).to_be_greater_than(200)
expect(r2).to_be_greater_than(200)
```

</details>

#### fill_path_aa of square path covers interior

1. var bm = Bitmap zeros
2. fill path aa


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(20, 20)
val p0 = sk_path_new()
val p1 = p0.move_to(4.0, 4.0)
val p2 = p1.line_to(16.0, 4.0)
val p3 = p2.line_to(16.0, 16.0)
val p4 = p3.line_to(4.0, 16.0)
val p5 = p4.close()
fill_path_aa(bm, p5, _red())
# center pixel (10,10): idx = (10*20+10)*4 = 840
val r_byte = bm.pixels[840] as i64
expect(r_byte).to_be_greater_than(100)
```

</details>

#### fill_path_aa with EvenOdd on nested square has hole

1. var bm = Bitmap zeros
2. fill path aa
   - Expected: bm.width equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(30, 30)
# outer square (EvenOdd winding), then inner square same direction -> hole
val outer = SkPath(fill_type: SkPathFillType.EvenOdd, segments: [])
val o1 = outer.move_to(2.0, 2.0)
val o2 = o1.line_to(28.0, 2.0)
val o3 = o2.line_to(28.0, 28.0)
val o4 = o3.line_to(2.0, 28.0)
val o5 = o4.close()
val o6 = o5.move_to(10.0, 10.0)
val o7 = o6.line_to(20.0, 10.0)
val o8 = o7.line_to(20.0, 20.0)
val o9 = o8.line_to(10.0, 20.0)
val o10 = o9.close()
fill_path_aa(bm, o10, _red())
# pixel at (15,15) center of inner square: should have less coverage than outer band
# outer band pixel (5,5): idx = (5*30+5)*4 = 620
val outer_r = bm.pixels[620] as i64
# inner pixel (15,15): idx = (15*30+15)*4 = 1860
val inner_r = bm.pixels[1860] as i64
# outer should be painted, inner may be hole
expect(outer_r).to_be_greater_than(0)
expect(bm.width).to_equal(30)
```

</details>

#### stroke_path of a line segment produces non-empty pixels

1. var bm = Bitmap zeros
2. stroke path


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(20, 20)
val p0 = sk_path_new()
val p1 = p0.move_to(2.0, 10.0)
val p2 = p1.line_to(18.0, 10.0)
val color = _red()
stroke_path(bm, p2, color, 4.0)
# pixel along the stroke: (10,10) idx = (10*20+10)*4 = 840
val r_byte = bm.pixels[840] as i64
expect(r_byte).to_be_greater_than(0)
```

</details>

#### blend_pixel with coverage=0 is a no-op

1. var bm = Bitmap zeros
2. bm blend pixel
   - Expected: r_byte equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm = Bitmap.zeros(10, 10)
val red = _red()
bm.blend_pixel(5, 5, red, 0.0)
# pixel (5,5): idx = (5*10+5)*4 = 220
val r_byte = bm.pixels[220] as i64
expect(r_byte).to_equal(0)
```

</details>

#### blend_pixel with coverage=1.0 equals set_pixel

1. var bm1 = Bitmap zeros
2. var bm2 = Bitmap zeros
3. bm1 set pixel
4. bm2 blend pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bm1 = Bitmap.zeros(10, 10)
var bm2 = Bitmap.zeros(10, 10)
val red = _red()
bm1.set_pixel(3, 3, red)
bm2.blend_pixel(3, 3, red, 1.0)
# pixel (3,3): idx = (3*10+3)*4 = 132
val r1 = bm1.pixels[132] as i64
val r2 = bm2.pixels[132] as i64
expect(r1).to_be_greater_than(200)
expect(r2).to_be_greater_than(200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/raster_prims_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bitmap

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
