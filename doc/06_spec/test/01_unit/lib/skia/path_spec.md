# Skia Path Specification

> Tests for SkPath construction and path-building operations.

<!-- sdn-diagram:id=path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

path_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Path Specification

Tests for SkPath construction and path-building operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-005 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkPath construction and path-building operations.

## Scenarios

### SkPath construction

#### sk_path_new creates empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
expect(p.is_empty()).to_equal(true)
```

</details>

#### sk_path_new has Winding fill type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
expect(p.fill_type).to_equal(SkPathFillType.Winding)
```

</details>

#### empty path has 0 verbs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
expect(p.count_verbs()).to_equal(0)
```

</details>

### SkPath move_to and line_to

#### move_to adds one verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0)
expect(p.count_verbs()).to_equal(1)
```

</details>

#### move_to is not empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(10.0, 20.0)
expect(p.is_empty()).to_equal(false)
```

</details>

#### line_to adds a verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
val p2 = p.move_to(0.0, 0.0).line_to(100.0, 0.0)
expect(p2.count_verbs()).to_equal(2)
```

</details>

#### verb kind for move is Move

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0)
val seg = p.segments[0]
expect(seg.verb).to_equal(SkPathVerb.Move)
```

</details>

#### verb kind for line is Line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0).line_to(100.0, 0.0)
val seg = p.segments[1]
expect(seg.verb).to_equal(SkPathVerb.Line)
```

</details>

### SkPath quad_to and cubic_to

#### quad_to adds a Quad verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0).quad_to(50.0, 50.0, 100.0, 0.0)
expect(p.count_verbs()).to_equal(2)
val seg = p.segments[1]
expect(seg.verb).to_equal(SkPathVerb.Quad)
```

</details>

#### quad_to stores two control points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0).quad_to(50.0, 50.0, 100.0, 0.0)
val seg = p.segments[1]
expect(seg.pts.len()).to_equal(2)
```

</details>

#### cubic_to adds a Cubic verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0).cubic_to(25.0, 75.0, 75.0, 75.0, 100.0, 0.0)
val seg = p.segments[1]
expect(seg.verb).to_equal(SkPathVerb.Cubic)
```

</details>

#### cubic_to stores three points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0).cubic_to(25.0, 75.0, 75.0, 75.0, 100.0, 0.0)
val seg = p.segments[1]
expect(seg.pts.len()).to_equal(3)
```

</details>

### SkPath close

#### close adds a Close verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().move_to(0.0, 0.0).line_to(100.0, 0.0).close()
val seg = p.segments[2]
expect(seg.verb).to_equal(SkPathVerb.Close)
```

</details>

### SkPath fill_type

#### with_fill_type changes fill type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new().with_fill_type(SkPathFillType.EvenOdd)
expect(p.fill_type).to_equal(SkPathFillType.EvenOdd)
```

</details>

#### with_fill_type is immutable — original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
val _ = p.with_fill_type(SkPathFillType.EvenOdd)
expect(p.fill_type).to_equal(SkPathFillType.Winding)
```

</details>

### SkPath immutability

#### move_to does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
val _ = p.move_to(0.0, 0.0)
expect(p.is_empty()).to_equal(true)
```

</details>

#### line_to chaining returns new path each time

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p0 = sk_path_new()
val p1 = p0.move_to(0.0, 0.0)
val p2 = p1.line_to(100.0, 0.0)
expect(p0.count_verbs()).to_equal(0)
expect(p1.count_verbs()).to_equal(1)
expect(p2.count_verbs()).to_equal(2)
```

</details>

### SkPath bounds

#### empty path has degenerate bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
val b = p.bounds()
expect(b.left).to_equal(0.0)
expect(b.right).to_equal(0.0)
```

</details>

#### rectangle path reports corner bounds

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
   - Expected: b.left equals `10.0`
   - Expected: b.top equals `20.0`
   - Expected: b.right equals `110.0`
   - Expected: b.bottom equals `70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(10.0, 20.0)
    .line_to(110.0, 20.0)
    .line_to(110.0, 70.0)
    .line_to(10.0, 70.0)
    .close()
val b = p.bounds()
expect(b.left).to_equal(10.0)
expect(b.top).to_equal(20.0)
expect(b.right).to_equal(110.0)
expect(b.bottom).to_equal(70.0)
```

</details>

### SkPath contains

#### point inside a rectangular path returns true

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
   - Expected: p contains `50.0, 25.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(100.0, 50.0)
    .line_to(0.0, 50.0)
    .close()
expect(p.contains(50.0, 25.0)).to_equal(true)
```

</details>

#### point outside the bounding box returns false

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
   - Expected: p does not contain `200.0, 25.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(100.0, 50.0)
    .line_to(0.0, 50.0)
    .close()
expect(p.contains(200.0, 25.0)).to_equal(false)
```

</details>

#### point far above the bounding box returns false

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
   - Expected: p does not contain `50.0, -10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(100.0, 50.0)
    .line_to(0.0, 50.0)
    .close()
expect(p.contains(50.0, -10.0)).to_equal(false)
```

</details>

#### point on the top edge of a rectangle returns true (half-open span)

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
   - Expected: p contains `50.0, 0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(100.0, 50.0)
    .line_to(0.0, 50.0)
    .close()
expect(p.contains(50.0, 0.0)).to_equal(true)
```

</details>

#### point inside a triangle returns true

1.  move to
2.  line to
3.  line to
4.  close
   - Expected: p contains `50.0, 20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(50.0, 80.0)
    .close()
expect(p.contains(50.0, 20.0)).to_equal(true)
```

</details>

#### point outside a triangle (but inside bbox) returns false

1.  move to
2.  line to
3.  line to
4.  close
   - Expected: p does not contain `5.0, 70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(50.0, 80.0)
    .close()
# Near the bottom-left corner of bbox, outside the triangle's slant.
expect(p.contains(5.0, 70.0)).to_equal(false)
```

</details>

#### point in the concave notch of a C-shape returns false

1.  move to
2.  line to
3.  line to
4.  line to
5.  line to
6.  line to
7.  line to
8.  line to
9.  close
   - Expected: p does not contain `70.0, 50.0`
   - Expected: p contains `20.0, 50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# C-shape: a 100x100 square with a rectangular bite taken out of its
# right side from (40, 25) to (100, 75).
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(100.0, 25.0)
    .line_to(40.0, 25.0)
    .line_to(40.0, 75.0)
    .line_to(100.0, 75.0)
    .line_to(100.0, 100.0)
    .line_to(0.0, 100.0)
    .close()
# Point in the notch: x > 40, 25 < y < 75.
expect(p.contains(70.0, 50.0)).to_equal(false)
# Sanity check — a point in the solid spine of the C is inside.
expect(p.contains(20.0, 50.0)).to_equal(true)
```

</details>

#### closed path with hole — point inside hole returns false (even-odd rule)

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
6.  move to
7.  line to
8.  line to
9.  line to
10.  close
   - Expected: p does not contain `50.0, 50.0`
   - Expected: p contains `10.0, 50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Outer 100x100 square + inner 40x40 hole, both wound CW.
# Under EvenOdd fill, the inner region is "outside".
val outer = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
    .line_to(100.0, 100.0)
    .line_to(0.0, 100.0)
    .close()
    .move_to(30.0, 30.0)
    .line_to(70.0, 30.0)
    .line_to(70.0, 70.0)
    .line_to(30.0, 70.0)
    .close()
val p = outer.with_fill_type(SkPathFillType.EvenOdd)
# Inside the hole: outside per even-odd.
expect(p.contains(50.0, 50.0)).to_equal(false)
# Between outer and hole: inside per even-odd.
expect(p.contains(10.0, 50.0)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
