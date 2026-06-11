# Render Widget Host View Specification

> 1. expect rwhv pending input count

<!-- sdn-diagram:id=render_widget_host_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_widget_host_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_widget_host_view_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_widget_host_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Widget Host View Specification

## Scenarios

### RenderWidgetHostView.new

#### new RWHV has 0 pending inputs

1. expect rwhv pending input count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rwhv = RenderWidgetHostView.new(_surface_id(), _rect(), _dc())
expect rwhv.pending_input_count() to_equal 0
```

</details>

#### bounds round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = SkRect(left: 10.0, top: 20.0, right: 500.0, bottom: 400.0)
val rwhv = RenderWidgetHostView.new(_surface_id(), bounds, _dc())
expect rwhv.bounds.left to_equal 10.0
```

</details>

### RenderWidgetHostView input

#### dispatch_input bumps pending count

1. var rwhv = RenderWidgetHostView new
2. rwhv dispatch input
3. expect rwhv pending input count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rwhv = RenderWidgetHostView.new(_surface_id(), _rect(), _dc())
val ev = InputEvent(kind: InputEventKind.MouseDown, x: 100, y: 200, data: 0)
rwhv.dispatch_input(ev)
expect rwhv.pending_input_count() to_equal 1
```

</details>

#### submit_compositor_frame returns without error

1. var rwhv = RenderWidgetHostView new
2. rwhv submit compositor frame
3. expect rwhv pending input count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rwhv = RenderWidgetHostView.new(_surface_id(), _rect(), _dc())
val frame = CompositorFrame.empty()
rwhv.submit_compositor_frame(frame)
expect rwhv.pending_input_count() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/content/render_widget_host_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RenderWidgetHostView.new
- RenderWidgetHostView input

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
