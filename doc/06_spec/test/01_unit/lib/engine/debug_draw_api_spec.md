# debug_draw_api_spec

> Engine Render — DebugDrawBuffer Tests

<!-- sdn-diagram:id=debug_draw_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_draw_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_draw_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_draw_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# debug_draw_api_spec

Engine Render — DebugDrawBuffer Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/debug_draw_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Render — DebugDrawBuffer Tests

Tests line, box, circle, cross drawing, lifetime expiration, and clear.

## Scenarios

### DebugColor

#### creates preset colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = DebugColor.red()
expect(r.r).to_equal(1.0)
expect(r.g).to_equal(0.0)

val g = DebugColor.green()
expect(g.g).to_equal(1.0)

val b = DebugColor.blue()
expect(b.b).to_equal(1.0)

val w = DebugColor.white()
expect(w.r).to_equal(1.0)
expect(w.g).to_equal(1.0)
expect(w.b).to_equal(1.0)

val y = DebugColor.yellow()
expect(y.r).to_equal(1.0)
expect(y.g).to_equal(1.0)
expect(y.b).to_equal(0.0)
```

</details>

### DebugDrawBuffer

#### draws a single line

1. var buf = DebugDrawBuffer new
2. buf draw line
   - Expected: buf.entry_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val s = Vec2(x: 0.0, y: 0.0)
val e = Vec2(x: 10.0, y: 10.0)
buf.draw_line(s, e, DebugColor.red(), 1.0)
expect(buf.entry_count()).to_equal(1)
```

</details>

#### draws a box as 4 lines

1. var buf = DebugDrawBuffer new
2. buf draw box
   - Expected: buf.entry_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val c = Vec2(x: 5.0, y: 5.0)
buf.draw_box(c, 2.0, 3.0, DebugColor.green(), 1.0)
expect(buf.entry_count()).to_equal(4)
```

</details>

#### draws a circle as 16 line segments

1. var buf = DebugDrawBuffer new
2. buf draw circle
   - Expected: buf.entry_count() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val c = Vec2(x: 0.0, y: 0.0)
buf.draw_circle(c, 5.0, DebugColor.blue(), 1.0)
expect(buf.entry_count()).to_equal(16)
```

</details>

#### draws a cross as 2 lines

1. var buf = DebugDrawBuffer new
2. buf draw cross
   - Expected: buf.entry_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val c = Vec2(x: 0.0, y: 0.0)
buf.draw_cross(c, 4.0, DebugColor.yellow(), 1.0)
expect(buf.entry_count()).to_equal(2)
```

</details>

#### respects max_entries limit

1. var buf = DebugDrawBuffer new
2. buf draw line
3. buf draw line
4. buf draw line
   - Expected: buf.entry_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(2)
val p = Vec2(x: 0.0, y: 0.0)
buf.draw_line(p, p, DebugColor.white(), 1.0)
buf.draw_line(p, p, DebugColor.white(), 1.0)
buf.draw_line(p, p, DebugColor.white(), 1.0)
expect(buf.entry_count()).to_equal(2)
```

</details>

#### removes expired entries on update

1. var buf = DebugDrawBuffer new
2. buf draw line
3. buf draw line
4. buf update
   - Expected: buf.entry_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val p = Vec2(x: 0.0, y: 0.0)
buf.draw_line(p, p, DebugColor.red(), 0.5)
buf.draw_line(p, p, DebugColor.green(), 2.0)
buf.update(1.0)
expect(buf.entry_count()).to_equal(1)
```

</details>

#### decrements lifetime on update

1. var buf = DebugDrawBuffer new
2. buf draw line
3. buf update
   - Expected: entries[0].lifetime equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val p = Vec2(x: 0.0, y: 0.0)
buf.draw_line(p, p, DebugColor.red(), 3.0)
buf.update(1.0)
val entries = buf.get_entries()
expect(entries[0].lifetime).to_equal(2.0)
```

</details>

#### clears all entries

1. var buf = DebugDrawBuffer new
2. buf draw line
3. buf draw line
4. buf clear
   - Expected: buf.entry_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val p = Vec2(x: 0.0, y: 0.0)
buf.draw_line(p, p, DebugColor.red(), 1.0)
buf.draw_line(p, p, DebugColor.green(), 1.0)
buf.clear()
expect(buf.entry_count()).to_equal(0)
```

</details>

#### returns entries via get_entries

1. var buf = DebugDrawBuffer new
2. buf draw line
   - Expected: entries.len() equals `1`
   - Expected: entries[0].line.start.x equals `1.0`
   - Expected: entries[0].line.end_point.x equals `3.0`
   - Expected: entries[0].lifetime equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = DebugDrawBuffer.new(100)
val s = Vec2(x: 1.0, y: 2.0)
val e = Vec2(x: 3.0, y: 4.0)
buf.draw_line(s, e, DebugColor.white(), 5.0)
val entries = buf.get_entries()
expect(entries.len()).to_equal(1)
expect(entries[0].line.start.x).to_equal(1.0)
expect(entries[0].line.end_point.x).to_equal(3.0)
expect(entries[0].lifetime).to_equal(5.0)
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
