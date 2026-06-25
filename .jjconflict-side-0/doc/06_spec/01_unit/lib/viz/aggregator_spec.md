# Aggregator Specification

> 1. expect agg known frames len

<!-- sdn-diagram:id=aggregator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aggregator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aggregator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aggregator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aggregator Specification

## Scenarios

### Aggregator

#### new Aggregator has 0 known_frames

1. expect agg known frames len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val agg = Aggregator.new()
expect agg.known_frames.len() to_equal 0
```

</details>

#### register_frame adds one entry

1. var agg = Aggregator new
2. agg register frame
3. expect agg known frames len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var agg = Aggregator.new()
val sid = _sid(1, 2, 0, 1)
val entry = AggregatorEntry(surface_id: sid, frame: CompositorFrame.empty())
agg.register_frame(entry)
expect agg.known_frames.len() to_equal 1
```

</details>

#### register_frame with duplicate SurfaceId replaces, size stays 1

1. var agg = Aggregator new
2. agg register frame
3. agg register frame
4. expect agg known frames len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var agg = Aggregator.new()
val sid = _sid(1, 2, 0, 1)
val entry1 = AggregatorEntry(surface_id: sid, frame: _frame_with_passes(1))
val entry2 = AggregatorEntry(surface_id: sid, frame: _frame_with_passes(3))
agg.register_frame(entry1)
agg.register_frame(entry2)
expect agg.known_frames.len() to_equal 1
```

</details>

#### aggregate with unknown root returns empty frame

1. var agg = Aggregator new
2. expect result render pass list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var agg = Aggregator.new()
val unknown = _sid(99, 99, 0, 0)
val result = agg.aggregate(unknown)
expect result.render_pass_list.len() to_equal 0
```

</details>

#### aggregate with known root returns that frame's pass count

1. var agg = Aggregator new
2. agg register frame
3. expect result render pass list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var agg = Aggregator.new()
val sid = _sid(1, 1, 0, 1)
val entry = AggregatorEntry(surface_id: sid, frame: _frame_with_passes(2))
agg.register_frame(entry)
val result = agg.aggregate(sid)
expect result.render_pass_list.len() to_equal 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/aggregator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Aggregator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
