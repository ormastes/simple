# Lod Specification

> <details>

<!-- sdn-diagram:id=lod_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lod_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lod_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lod_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lod Specification

## Scenarios

### LODLevel

#### creates a level with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lod = LODLevel.new(0, 50.0, "high")
expect(lod.level).to_equal(0)
expect(lod.max_distance).to_equal(50.0)
expect(lod.detail_name).to_equal("high")
```

</details>

### LODGroup

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = LODGroup.new("tree")
expect(group.level_count()).to_equal(0)
expect(group.name).to_equal("tree")
```

</details>

#### adds levels sorted by distance

1. var group = LODGroup new
2. group add level
3. group add level
4. group add level
   - Expected: group.level_count() equals `3`
   - Expected: group.levels[0].detail_name equals `high`
   - Expected: group.levels[1].detail_name equals `medium`
   - Expected: group.levels[2].detail_name equals `low`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var group = LODGroup.new("tree")
group.add_level(2, 200.0, "low")
group.add_level(0, 50.0, "high")
group.add_level(1, 100.0, "medium")
expect(group.level_count()).to_equal(3)
expect(group.levels[0].detail_name).to_equal("high")
expect(group.levels[1].detail_name).to_equal("medium")
expect(group.levels[2].detail_name).to_equal("low")
```

</details>

#### selects correct level for close distance

1. var group = LODGroup new
2. group add level
3. group add level
4. group add level
   - Expected: group.select_level(25.0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var group = LODGroup.new("building")
group.add_level(0, 50.0, "high")
group.add_level(1, 100.0, "medium")
group.add_level(2, 200.0, "low")
expect(group.select_level(25.0)).to_equal(0)
```

</details>

#### selects correct level for mid distance

1. var group = LODGroup new
2. group add level
3. group add level
4. group add level
   - Expected: group.select_level(75.0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var group = LODGroup.new("building")
group.add_level(0, 50.0, "high")
group.add_level(1, 100.0, "medium")
group.add_level(2, 200.0, "low")
expect(group.select_level(75.0)).to_equal(1)
```

</details>

#### selects last level for far distance

1. var group = LODGroup new
2. group add level
3. group add level
4. group add level
   - Expected: group.select_level(999.0) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var group = LODGroup.new("building")
group.add_level(0, 50.0, "high")
group.add_level(1, 100.0, "medium")
group.add_level(2, 200.0, "low")
expect(group.select_level(999.0)).to_equal(2)
```

</details>

#### returns detail name for valid level

1. var group = LODGroup new
2. group add level
3. group add level
   - Expected: group.get_detail_name(0) equals `detailed`
   - Expected: group.get_detail_name(1) equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var group = LODGroup.new("rock")
group.add_level(0, 30.0, "detailed")
group.add_level(1, 80.0, "simple")
expect(group.get_detail_name(0)).to_equal("detailed")
expect(group.get_detail_name(1)).to_equal("simple")
```

</details>

#### returns unknown for invalid level

1. var group = LODGroup new
2. group add level
   - Expected: group.get_detail_name(99) equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var group = LODGroup.new("rock")
group.add_level(0, 30.0, "detailed")
expect(group.get_detail_name(99)).to_equal("unknown")
```

</details>

### LODManager

#### starts with zero groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = LODManager.new()
expect(mgr.group_count()).to_equal(0)
```

</details>

#### adds a group and returns its index

1. var mgr = LODManager new
2. var grp = LODGroup new
3. grp add level
   - Expected: idx equals `0`
   - Expected: mgr.group_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LODManager.new()
var grp = LODGroup.new("tree")
grp.add_level(0, 50.0, "high")
val idx = mgr.add_group(grp)
expect(idx).to_equal(0)
expect(mgr.group_count()).to_equal(1)
```

</details>

#### selects LOD for a group by distance

1. var mgr = LODManager new
2. var grp = LODGroup new
3. grp add level
4. grp add level
   - Expected: mgr.select_for_distance(idx, 10.0) equals `0`
   - Expected: mgr.select_for_distance(idx, 80.0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LODManager.new()
var grp = LODGroup.new("rock")
grp.add_level(0, 40.0, "high")
grp.add_level(1, 120.0, "low")
val idx = mgr.add_group(grp)
expect(mgr.select_for_distance(idx, 10.0)).to_equal(0)
expect(mgr.select_for_distance(idx, 80.0)).to_equal(1)
```

</details>

#### returns 0 for invalid group index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = LODManager.new()
expect(mgr.select_for_distance(99, 10.0)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/lod_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LODLevel
- LODGroup
- LODManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
