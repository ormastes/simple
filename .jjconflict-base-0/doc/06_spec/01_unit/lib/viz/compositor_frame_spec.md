# Compositor Frame Specification

> 1. expect f render pass list len

<!-- sdn-diagram:id=compositor_frame_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compositor_frame_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compositor_frame_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compositor_frame_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Frame Specification

## Scenarios

### CompositorFrame::empty

#### empty frame has 0 passes

1. expect f render pass list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = CompositorFrame.empty()
expect f.render_pass_list.len() to_equal 0
```

</details>

#### empty frame total_quad_count is 0

1. expect f total quad count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = CompositorFrame.empty()
expect f.total_quad_count() to_equal 0
```

</details>

#### empty frame root_render_pass_id is -1

1. expect f root render pass id


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = CompositorFrame.empty()
expect f.root_render_pass_id() to_equal -1
```

</details>

### CompositorFrame with passes

#### adding one RenderPass bumps pass count

1. var f = CompositorFrame empty
2. expect f render pass list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = CompositorFrame.empty()
val rp = RenderPass.new(1, _rect(0.0, 0.0, 800.0, 600.0))
f.render_pass_list = f.render_pass_list + [rp]
expect f.render_pass_list.len() to_equal 1
```

</details>

#### root_render_pass_id returns last pass id

1. var f = CompositorFrame empty
2. expect f root render pass id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = CompositorFrame.empty()
val rp1 = RenderPass.new(10, _rect(0.0, 0.0, 800.0, 600.0))
val rp2 = RenderPass.new(20, _rect(0.0, 0.0, 800.0, 600.0))
f.render_pass_list = f.render_pass_list + [rp1, rp2]
expect f.root_render_pass_id() to_equal 20
```

</details>

#### total_quad_count sums across multiple passes

1. var f = CompositorFrame empty
2. var rp1 = RenderPass new
3. var rp2 = RenderPass new
4. rp1 add quad
5. rp1 add quad
6. rp2 add quad
7. expect f total quad count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = CompositorFrame.empty()
var rp1 = RenderPass.new(1, _rect(0.0, 0.0, 100.0, 100.0))
var rp2 = RenderPass.new(2, _rect(0.0, 0.0, 100.0, 100.0))
val color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val q = DrawQuad.solid_color(0, _rect(0.0, 0.0, 50.0, 50.0), color)
rp1.add_quad(q)
rp1.add_quad(q)
rp2.add_quad(q)
f.render_pass_list = f.render_pass_list + [rp1, rp2]
expect f.total_quad_count() to_equal 3
```

</details>

### FrameMetadata

#### fields round-trip through constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = FrameMetadata(
    device_scale_factor: 2.0,
    root_scroll_offset_x: 10.5,
    root_scroll_offset_y: 20.0,
    frame_token: 7
)
expect meta.device_scale_factor to_equal 2.0
expect meta.frame_token to_equal 7
```

</details>

### RenderPass::new

#### new(42, rect) has id=42

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rp = RenderPass.new(42, _rect(0.0, 0.0, 100.0, 100.0))
expect rp.id to_equal 42
```

</details>

#### new pass starts with 0 quads

1. expect rp quad count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rp = RenderPass.new(1, _rect(0.0, 0.0, 100.0, 100.0))
expect rp.quad_count() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/compositor_frame_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CompositorFrame::empty
- CompositorFrame with passes
- FrameMetadata
- RenderPass::new

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
