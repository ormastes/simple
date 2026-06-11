# Terrain Specification

> 1. var td = TerrainData new

<!-- sdn-diagram:id=terrain_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terrain_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terrain_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terrain_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terrain Specification

## Scenarios

### TerrainData

#### creates flat terrain with correct cell count

1. var td = TerrainData new
   - Expected: td.cell_count() equals `64`
   - Expected: td.get_height(0, 0) equals `0.0`
   - Expected: td.get_height(4, 4) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(8, 8, 100.0)
expect(td.cell_count()).to_equal(64)
expect(td.get_height(0, 0)).to_equal(0.0)
expect(td.get_height(4, 4)).to_equal(0.0)
```

</details>

#### sets and gets individual cell heights

1. var td = TerrainData new
2. td set height
   - Expected: td.get_height(2, 3) equals `25.5`
   - Expected: td.get_height(0, 0) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(4, 4, 50.0)
td.set_height(2, 3, 25.5)
expect(td.get_height(2, 3)).to_equal(25.5)
expect(td.get_height(0, 0)).to_equal(0.0)
```

</details>

#### clamps height to max

1. var td = TerrainData new
2. td set height
   - Expected: td.get_height(1, 1) equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(4, 4, 10.0)
td.set_height(1, 1, 999.0)
expect(td.get_height(1, 1)).to_equal(10.0)
```

</details>

#### clamps negative height to zero

1. var td = TerrainData new
2. td set height
   - Expected: td.get_height(1, 1) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(4, 4, 10.0)
td.set_height(1, 1, -5.0)
expect(td.get_height(1, 1)).to_equal(0.0)
```

</details>

#### ignores out-of-bounds set

1. var td = TerrainData new
2. td set height
   - Expected: td.get_height(10, 10) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(4, 4, 10.0)
td.set_height(10, 10, 5.0)
expect(td.get_height(10, 10)).to_equal(0.0)
```

</details>

#### raises area around center

1. var td = TerrainData new
2. td raise area


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(8, 8, 100.0)
td.raise_area(4, 4, 1, 10.0)
expect(td.get_height(4, 4)).to_be_greater_than(0.0)
```

</details>

#### flattens area to target height

1. var td = TerrainData new
2. td set height
3. td set height
4. td flatten area
   - Expected: td.get_height(4, 4) equals `30.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(8, 8, 100.0)
td.set_height(3, 3, 50.0)
td.set_height(4, 4, 20.0)
td.flatten_area(4, 4, 2, 30.0)
expect(td.get_height(4, 4)).to_equal(30.0)
```

</details>

#### manages texture layers

1. var td = TerrainData new
2. td add layer
3. td add layer
   - Expected: td.layer_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var td = TerrainData.new(4, 4, 10.0)
td.add_layer("grass", 10.0, 0.0, 0.5)
td.add_layer("rock", 5.0, 0.8, 0.2)
expect(td.layer_count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/terrain_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TerrainData

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
