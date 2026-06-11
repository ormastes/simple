# Layer Tree Host Specification

> <details>

<!-- sdn-diagram:id=layer_tree_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layer_tree_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layer_tree_host_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layer_tree_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Tree Host Specification

## Scenarios

### LayerTreeImpl

#### empty

#### has 0 layers when created empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = LayerTreeImpl.empty()
expect(tree.layer_count()).to_equal(0)
```

</details>

#### add_layer

#### add_layer returns monotonically increasing ids

1. var tree = LayerTreeImpl empty
   - Expected: id2 > id1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = LayerTreeImpl.empty()
val bounds = SkRect.make_xywh(0.0, 0.0, 100.0, 100.0)
val l1 = Layer.root(bounds)
val l2 = Layer.root(bounds)
val id1 = tree.add_layer(l1)
val id2 = tree.add_layer(l2)
expect(id2 > id1).to_equal(true)
```

</details>

#### layer_count grows after add_layer

1. var tree = LayerTreeImpl empty
2. tree add layer
   - Expected: tree.layer_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = LayerTreeImpl.empty()
val bounds = SkRect.make_xywh(0.0, 0.0, 50.0, 50.0)
val l = Layer.root(bounds)
tree.add_layer(l)
expect(tree.layer_count()).to_equal(1)
```

</details>

### LayerTreeHost

#### new

#### starts with needs_commit=false and source_frame_number=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = LayerTreeHost.new()
expect(host.needs_commit).to_equal(false)
expect(host.source_frame_number).to_equal(0)
```

</details>

#### set_needs_commit and commit

#### set_needs_commit sets flag then commit clears it

1. var host = LayerTreeHost new
2. host set needs commit
   - Expected: host.needs_commit is true
3. host commit
   - Expected: host.needs_commit is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = LayerTreeHost.new()
host.set_needs_commit()
expect(host.needs_commit).to_equal(true)
host.commit()
expect(host.needs_commit).to_equal(false)
```

</details>

#### commit copies pending to active

#### layer added to pending appears in active after commit

1. var host = LayerTreeHost new
2. host pending tree add layer
   - Expected: host.active_tree.layer_count() equals `0`
3. host commit
   - Expected: host.active_tree.layer_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = LayerTreeHost.new()
val bounds = SkRect.make_xywh(0.0, 0.0, 200.0, 200.0)
val l = Layer.root(bounds)
host.pending_tree.add_layer(l)
expect(host.active_tree.layer_count()).to_equal(0)
host.commit()
expect(host.active_tree.layer_count()).to_equal(1)
```

</details>

#### begin_main_frame

#### increments source_frame_number each call

1. var host = LayerTreeHost new
2. host begin main frame
   - Expected: host.source_frame_number equals `1`
3. host begin main frame
   - Expected: host.source_frame_number equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = LayerTreeHost.new()
host.begin_main_frame()
expect(host.source_frame_number).to_equal(1)
host.begin_main_frame()
expect(host.source_frame_number).to_equal(2)
```

</details>

#### tree independence

#### changing pending after commit does not mutate active

1. var host = LayerTreeHost new
2. host pending tree add layer
3. host commit
4. host pending tree add layer
   - Expected: host.active_tree.layer_count() equals `active_count_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = LayerTreeHost.new()
val bounds = SkRect.make_xywh(0.0, 0.0, 64.0, 64.0)
val l = Layer.root(bounds)
host.pending_tree.add_layer(l)
host.commit()
val active_count_before = host.active_tree.layer_count()
val l2 = Layer.root(bounds)
host.pending_tree.add_layer(l2)
expect(host.active_tree.layer_count()).to_equal(active_count_before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cc/layer_tree_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LayerTreeImpl
- LayerTreeHost

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
