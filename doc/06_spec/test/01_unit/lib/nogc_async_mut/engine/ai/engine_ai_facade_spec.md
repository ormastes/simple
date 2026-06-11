# Engine Ai Facade Specification

> 1. NavPoint

<!-- sdn-diagram:id=engine_ai_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_ai_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_ai_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_ai_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Ai Facade Specification

## Scenarios

### nogc_async_mut engine ai facade

#### re-exports navmesh geometry and path helpers

1. NavPoint
2. NavPoint
3. NavPoint
   - Expected: poly.contains_point(1.0, 1.0) is true
4. poly add neighbor
   - Expected: poly.has_neighbor(8) is true
5. var mesh = NavMesh new
6. NavPoint
7. NavPoint
8. NavPoint
9. NavPoint
10. NavPoint
11. NavPoint
12. mesh connect
   - Expected: mesh.polygon_count() equals `2`
   - Expected: mesh.find_polygon_at(1.0, 1.0) equals `left`
   - Expected: mesh.find_path(1.0, 1.0, 11.0, 1.0).length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = NavPoint(x: 0.0, y: 0.0)
val b = NavPoint(x: 3.0, y: 4.0)
expect(a.distance_to(b)).to_equal(5.0)

var poly = NavPolygon.new(7, [
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 0.0, y: 10.0)
])
expect(poly.center.x).to_be_greater_than(3.0)
expect(poly.contains_point(1.0, 1.0)).to_equal(true)
poly.add_neighbor(8)
expect(poly.has_neighbor(8)).to_equal(true)

var mesh = NavMesh.new()
val left = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 0.0, y: 10.0)
])
val right = mesh.add_polygon([
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 20.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0)
])
mesh.connect(left, right)
expect(mesh.polygon_count()).to_equal(2)
expect(mesh.find_polygon_at(1.0, 1.0)).to_equal(left)
expect(mesh.find_path(1.0, 1.0, 11.0, 1.0).length()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/ai/engine_ai_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine ai facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
