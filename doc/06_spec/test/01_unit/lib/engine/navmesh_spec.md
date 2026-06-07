# navmesh_spec

> Engine AI NavMesh — navigation mesh and A* pathfinding tests

<!-- sdn-diagram:id=navmesh_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=navmesh_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

navmesh_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=navmesh_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# navmesh_spec

Engine AI NavMesh — navigation mesh and A* pathfinding tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/navmesh_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine AI NavMesh — navigation mesh and A* pathfinding tests

Tests polygon creation, point containment, neighbor linking,
polygon lookup, and A* path finding through connected polygons.

## Scenarios

### NavPoint

#### distance_to computes euclidean distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = NavPoint(x: 0.0, y: 0.0)
val b = NavPoint(x: 3.0, y: 4.0)
val d = a.distance_to(b)
# Should be 5.0
expect(d).to_be_greater_than(4.99)
expect(d).to_be_less_than(5.01)
```

</details>

#### distance_to self is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = NavPoint(x: 5.0, y: 7.0)
val d = a.distance_to(a)
expect(d).to_be_greater_than(-0.01)
expect(d).to_be_less_than(0.01)
```

</details>

### NavPolygon

#### new computes center as vertex average

1. NavPoint
2. NavPoint
3. NavPoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val poly = NavPolygon.new(0, [
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 6.0, y: 0.0),
    NavPoint(x: 3.0, y: 6.0)
])
# Center should be (3.0, 2.0)
expect(poly.center.x).to_be_greater_than(2.99)
expect(poly.center.x).to_be_less_than(3.01)
expect(poly.center.y).to_be_greater_than(1.99)
expect(poly.center.y).to_be_less_than(2.01)
```

</details>

#### contains_point detects interior point

1. NavPoint
2. NavPoint
3. NavPoint
4. NavPoint
   - Expected: poly.contains_point(5.0, 5.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val poly = NavPolygon.new(0, [
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0),
    NavPoint(x: 0.0, y: 10.0)
])
expect(poly.contains_point(5.0, 5.0)).to_equal(true)
```

</details>

#### contains_point rejects exterior point

1. NavPoint
2. NavPoint
3. NavPoint
4. NavPoint
   - Expected: poly.contains_point(15.0, 5.0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val poly = NavPolygon.new(0, [
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0),
    NavPoint(x: 0.0, y: 10.0)
])
expect(poly.contains_point(15.0, 5.0)).to_equal(false)
```

</details>

### NavMesh

#### add_polygon creates polygon and returns id

1. var mesh = NavMesh new
2. NavPoint
3. NavPoint
4. NavPoint
5. NavPoint
6. NavPoint
7. NavPoint
   - Expected: id0 equals `0`
   - Expected: id1 equals `1`
   - Expected: mesh.polygon_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = NavMesh.new()
val id0 = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 5.0, y: 10.0)
])
val id1 = mesh.add_polygon([
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 20.0, y: 0.0),
    NavPoint(x: 15.0, y: 10.0)
])
expect(id0).to_equal(0)
expect(id1).to_equal(1)
expect(mesh.polygon_count()).to_equal(2)
```

</details>

#### connect links polygons bidirectionally

1. var mesh = NavMesh new
2. NavPoint
3. NavPoint
4. NavPoint
5. NavPoint
6. NavPoint
7. NavPoint
8. mesh connect
   - Expected: poly0.has_neighbor(id1) is true
   - Expected: poly1.has_neighbor(id0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = NavMesh.new()
val id0 = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 5.0, y: 10.0)
])
val id1 = mesh.add_polygon([
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 20.0, y: 0.0),
    NavPoint(x: 15.0, y: 10.0)
])
mesh.connect(id0, id1)
val p0 = mesh.get_polygon(id0)
val p1 = mesh.get_polygon(id1)
if val Some(poly0) = p0:
    expect(poly0.has_neighbor(id1)).to_equal(true)
if val Some(poly1) = p1:
    expect(poly1.has_neighbor(id0)).to_equal(true)
```

</details>

#### find_polygon_at locates correct polygon

1. var mesh = NavMesh new
2. NavPoint
3. NavPoint
4. NavPoint
5. NavPoint
   - Expected: mesh.find_polygon_at(5.0, 5.0) equals `id0`
   - Expected: mesh.find_polygon_at(15.0, 5.0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = NavMesh.new()
val id0 = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0),
    NavPoint(x: 0.0, y: 10.0)
])
expect(mesh.find_polygon_at(5.0, 5.0)).to_equal(id0)
expect(mesh.find_polygon_at(15.0, 5.0)).to_equal(-1)
```

</details>

#### find_path returns path through connected polygons

1. var mesh = NavMesh new
2. NavPoint
3. NavPoint
4. NavPoint
5. NavPoint
6. NavPoint
7. NavPoint
8. NavPoint
9. NavPoint
10. NavPoint
11. NavPoint
12. NavPoint
13. NavPoint
14. mesh connect
15. mesh connect
   - Expected: path.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = NavMesh.new()
# Three square polygons in a row: [0,10]x[0,10], [10,20]x[0,10], [20,30]x[0,10]
val id0 = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0),
    NavPoint(x: 0.0, y: 10.0)
])
val id1 = mesh.add_polygon([
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 20.0, y: 0.0),
    NavPoint(x: 20.0, y: 10.0),
    NavPoint(x: 10.0, y: 10.0)
])
val id2 = mesh.add_polygon([
    NavPoint(x: 20.0, y: 0.0),
    NavPoint(x: 30.0, y: 0.0),
    NavPoint(x: 30.0, y: 10.0),
    NavPoint(x: 20.0, y: 10.0)
])
mesh.connect(id0, id1)
mesh.connect(id1, id2)
val path = mesh.find_path(5.0, 5.0, 25.0, 5.0)
# Path should have 3 centers
expect(path.len()).to_equal(3)
```

</details>

#### find_path returns empty for disconnected polygons

1. var mesh = NavMesh new
2. NavPoint
3. NavPoint
4. NavPoint
5. NavPoint
6. NavPoint
7. NavPoint
8. NavPoint
9. NavPoint
   - Expected: path.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = NavMesh.new()
val id0 = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0),
    NavPoint(x: 0.0, y: 10.0)
])
val id1 = mesh.add_polygon([
    NavPoint(x: 50.0, y: 50.0),
    NavPoint(x: 60.0, y: 50.0),
    NavPoint(x: 60.0, y: 60.0),
    NavPoint(x: 50.0, y: 60.0)
])
# No connect — path should be empty
val path = mesh.find_path(5.0, 5.0, 55.0, 55.0)
expect(path.len()).to_equal(0)
```

</details>

#### find_path returns single center for same polygon

1. var mesh = NavMesh new
2. NavPoint
3. NavPoint
4. NavPoint
5. NavPoint
   - Expected: path.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = NavMesh.new()
val id0 = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0),
    NavPoint(x: 0.0, y: 10.0)
])
val path = mesh.find_path(2.0, 2.0, 8.0, 8.0)
expect(path.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
