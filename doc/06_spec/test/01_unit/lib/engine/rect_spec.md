# rect_spec

> Engine Rect2 — Rectangle Tests

<!-- sdn-diagram:id=rect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rect_spec

Engine Rect2 — Rectangle Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/rect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Rect2 — Rectangle Tests

Tests constructors, edges, containment, intersection, merge, expand.

## Scenarios

### Rect2

### constructors

#### creates with new

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.new(10.0, 20.0, 100.0, 50.0)
expect(r.x).to_equal(10.0)
expect(r.y).to_equal(20.0)
expect(r.width).to_equal(100.0)
expect(r.height).to_equal(50.0)
```

</details>

#### creates from center

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.from_center(50.0, 50.0, 20.0, 10.0)
expect(r.x).to_equal(40.0)
expect(r.y).to_equal(45.0)
expect(r.width).to_equal(20.0)
expect(r.height).to_equal(10.0)
```

</details>

### edge accessors

#### returns correct edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.new(10.0, 20.0, 30.0, 40.0)
expect(r.left()).to_equal(10.0)
expect(r.right()).to_equal(40.0)
expect(r.top()).to_equal(20.0)
expect(r.bottom()).to_equal(60.0)
```

</details>

### queries

#### contains interior point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.new(0.0, 0.0, 100.0, 100.0)
expect(r.contains_point(50.0, 50.0)).to_equal(true)
```

</details>

#### does not contain exterior point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.new(0.0, 0.0, 100.0, 100.0)
expect(r.contains_point(150.0, 50.0)).to_equal(false)
```

</details>

#### contains edge point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.new(0.0, 0.0, 100.0, 100.0)
expect(r.contains_point(0.0, 0.0)).to_equal(true)
expect(r.contains_point(100.0, 100.0)).to_equal(true)
```

</details>

### intersection

#### detects overlapping rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Rect2.new(0.0, 0.0, 10.0, 10.0)
val b = Rect2.new(5.0, 5.0, 10.0, 10.0)
expect(a.intersects(b)).to_equal(true)
```

</details>

#### detects non-overlapping rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Rect2.new(0.0, 0.0, 10.0, 10.0)
val b = Rect2.new(20.0, 20.0, 10.0, 10.0)
expect(a.intersects(b)).to_equal(false)
```

</details>

### merge and expand

#### merges two rects into bounding rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Rect2.new(0.0, 0.0, 10.0, 10.0)
val b = Rect2.new(20.0, 20.0, 10.0, 10.0)
val m = a.merge(b)
expect(m.x).to_equal(0.0)
expect(m.y).to_equal(0.0)
expect(m.right()).to_equal(30.0)
expect(m.bottom()).to_equal(30.0)
```

</details>

#### expands rect by margin

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rect2.new(10.0, 10.0, 20.0, 20.0)
val e = r.expand(5.0)
expect(e.x).to_equal(5.0)
expect(e.y).to_equal(5.0)
expect(e.width).to_equal(30.0)
expect(e.height).to_equal(30.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
