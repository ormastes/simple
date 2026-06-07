# Tile Manager Specification

> <details>

<!-- sdn-diagram:id=tile_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tile_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tile_manager_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tile_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tile Manager Specification

## Scenarios

### TileManager

#### new

#### new manager has 0 tiles and 0 ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = make_manager()
expect(mgr.tiles.len()).to_equal(0)
expect(mgr.ready_count()).to_equal(0)
```

</details>

#### add_tile

#### add_tile increments pending_count

1. var mgr = make manager
2. mgr add tile
   - Expected: mgr.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val t = make_tile(1, 0, 0, TilePriority.NowBin)
mgr.add_tile(t)
expect(mgr.pending_count()).to_equal(1)
```

</details>

#### schedule_tasks

#### schedule_tasks marks NowBin tiles ready

1. var mgr = make manager
2. mgr add tile
3. mgr schedule tasks
   - Expected: mgr.ready_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val t = make_tile(1, 0, 0, TilePriority.NowBin)
mgr.add_tile(t)
mgr.schedule_tasks()
expect(mgr.ready_count()).to_equal(1)
```

</details>

#### SoonBin tiles remain not-ready after schedule

1. var mgr = make manager
2. mgr add tile
3. mgr schedule tasks
   - Expected: mgr.ready_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val t = make_tile(1, 0, 0, TilePriority.SoonBin)
mgr.add_tile(t)
mgr.schedule_tasks()
expect(mgr.ready_count()).to_equal(0)
```

</details>

#### invalidate_tile

#### invalidate_tile flips is_ready back to false

1. var mgr = make manager
2. mgr add tile
3. mgr schedule tasks
   - Expected: mgr.ready_count() equals `1`
4. mgr invalidate tile
   - Expected: mgr.ready_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val key = TileKey.new(1, 0, 0, 1.0)
val t = make_tile(1, 0, 0, TilePriority.NowBin)
mgr.add_tile(t)
mgr.schedule_tasks()
expect(mgr.ready_count()).to_equal(1)
mgr.invalidate_tile(key)
expect(mgr.ready_count()).to_equal(0)
```

</details>

#### counts

#### ready_count + pending_count equals tile count

1. var mgr = make manager
2. mgr add tile
3. mgr add tile
4. mgr add tile
5. mgr schedule tasks
   - Expected: total equals `mgr.tiles.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val t1 = make_tile(1, 0, 0, TilePriority.NowBin)
val t2 = make_tile(1, 1, 0, TilePriority.SoonBin)
val t3 = make_tile(1, 0, 1, TilePriority.NowBin)
mgr.add_tile(t1)
mgr.add_tile(t2)
mgr.add_tile(t3)
mgr.schedule_tasks()
val total = mgr.ready_count() + mgr.pending_count()
expect(total).to_equal(mgr.tiles.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cc/tile_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TileManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
