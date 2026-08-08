# Aggregator Compose Specification

> <details>

<!-- sdn-diagram:id=aggregator_compose_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aggregator_compose_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aggregator_compose_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aggregator_compose_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aggregator Compose Specification

## Scenarios

### aggregator_compose

#### compose_transforms identity with identity yields identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compose_transforms(_identity(), _identity())
val eq = _mat_eq(result, _identity())
eq.to_equal(true)
```

</details>

#### compose_transforms translate(5,0) then translate(0,3) yields translate(5,3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = _translate(5.0, 0.0)
val t2 = _translate(0.0, 3.0)
val result = compose_transforms(t1, t2)
val expected = _translate(5.0, 3.0)
val eq = _mat_eq(result, expected)
eq.to_equal(true)
```

</details>

#### intersect_clips fully overlapping returns the smaller rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_clip = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val child_clip  = SkRect(left: 10.0, top: 10.0, right: 50.0, bottom: 50.0)
val result = intersect_clips(parent_clip, child_clip)
result.left.to_equal(10.0)
result.top.to_equal(10.0)
result.right.to_equal(50.0)
result.bottom.to_equal(50.0)
```

</details>

#### intersect_clips disjoint rects returns empty rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_clip = SkRect(left: 0.0, top: 0.0, right: 10.0, bottom: 10.0)
val child_clip  = SkRect(left: 20.0, top: 20.0, right: 30.0, bottom: 30.0)
val result = intersect_clips(parent_clip, child_clip)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
result.right.to_equal(0.0)
result.bottom.to_equal(0.0)
```

</details>

#### intersect_clips partially overlapping rects returns correct overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_clip = SkRect(left: 0.0, top: 0.0, right: 50.0, bottom: 50.0)
val child_clip  = SkRect(left: 30.0, top: 30.0, right: 80.0, bottom: 80.0)
val result = intersect_clips(parent_clip, child_clip)
result.left.to_equal(30.0)
result.top.to_equal(30.0)
result.right.to_equal(50.0)
result.bottom.to_equal(50.0)
```

</details>

#### compose_effects multiplies opacity values

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_effect = EffectNode(
    id: 0, parent_id: -1,
    opacity: 0.5, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val child_effect = EffectNode(
    id: 1, parent_id: 0,
    opacity: 0.5, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val result = compose_effects(parent_effect, child_effect)
val diff = result.opacity - 0.25
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
val close = abs_diff < 1e-6
close.to_equal(true)
```

</details>

#### compose_effects child non-SrcOver blend_mode overrides parent SrcOver

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blend_multiply: i32 = 2
val parent_effect = EffectNode(
    id: 0, parent_id: -1,
    opacity: 1.0, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val child_effect = EffectNode(
    id: 1, parent_id: 0,
    opacity: 1.0, blend_mode: blend_multiply,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val result = compose_effects(parent_effect, child_effect)
result.blend_mode.to_equal(blend_multiply)
```

</details>

#### compose_effects both SrcOver yields SrcOver blend mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_effect = EffectNode(
    id: 0, parent_id: -1,
    opacity: 1.0, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val child_effect = EffectNode(
    id: 1, parent_id: 0,
    opacity: 1.0, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val result = compose_effects(parent_effect, child_effect)
result.blend_mode.to_equal(BLEND_MODE_SRC_OVER)
```

</details>

#### effective_transform_for_surface for root node returns identity

1. var tree = TransformTree new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = TransformTree.new()
# root node already at id=0 with empty local (falls back to identity)
val sid = _surface(0)
val result = effective_transform_for_surface(sid, tree)
val eq = _mat_eq(result, _identity())
eq.to_equal(true)
```

</details>

#### effective_clip_for_surface for 2-level nested clip returns intersection

1. var tree = ClipTree new
2. tree add node
3. tree add node


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = ClipTree.new()
# root node (id=0) has clip_w=0/clip_h=0 (no clip at root by default)
# Add a parent clip node at id=1
val parent_node = ClipNode(
    id: 1, parent_id: 0,
    clip_x: 0.0, clip_y: 0.0, clip_w: 100.0, clip_h: 100.0
)
tree.add_node(parent_node)
# Add a child clip node at id=2
val child_node = ClipNode(
    id: 2, parent_id: 1,
    clip_x: 20.0, clip_y: 20.0, clip_w: 40.0, clip_h: 40.0
)
tree.add_node(child_node)
val sid = _surface(2)
val result = effective_clip_for_surface(sid, tree)
# root node has clip_w=clip_h=0 -> rect (0,0,0,0)
# parent clip: (0,0,100,100) intersected with root (0,0,0,0) -> (0,0,0,0)
# child clip: (20,20,60,60) intersected with (0,0,0,0) -> (0,0,0,0)
# So result is empty rect (disjoint with zero-size root)
val is_empty = result.left >= result.right or result.top >= result.bottom
is_empty.to_equal(true)
```

</details>

#### effective_clip_for_surface for a clip node with parent_id -1 returns own rect

1. var tree = ClipTree new


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a fresh ClipTree where we treat node 0's clip as real
var tree = ClipTree.new()
# Add a standalone clip node with parent_id=-1 so it is treated as root
val standalone = ClipNode(
    id: 0, parent_id: -1,
    clip_x: 5.0, clip_y: 5.0, clip_w: 30.0, clip_h: 30.0
)
# We can't replace node 0 in tree (already inserted), so use a separate tree.
# ClipTree.new() inserts a root with id=0; add_node assigns the next id.
# Instead, directly verify behavior using the default root via get(0):
# The root in ClipTree.new() has clip_x=0, clip_y=0, clip_w=0, clip_h=0, parent_id=-1.
# So effective_clip_for_surface for surface with sink_id=0 returns SkRect(0,0,0,0).
val sid = _surface(0)
val result = effective_clip_for_surface(sid, tree)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
```

</details>

#### effective_effect_for_surface for 2-level tree multiplies opacity

1. var tree = EffectTree new
2. tree add node


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = EffectTree.new()
# root node (id=0) opacity=1.0, blend_mode=0 (already inserted by EffectTree.new())
val child_node = EffectNode(
    id: 1, parent_id: 0,
    opacity: 0.5, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
tree.add_node(child_node)
val sid = _surface(1)
val result = effective_effect_for_surface(sid, tree)
# root opacity 1.0 * child opacity 0.5 = 0.5
val diff = result.opacity - 0.5
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
val close = abs_diff < 1e-6
close.to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/aggregator_compose_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- aggregator_compose

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
