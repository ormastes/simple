# Frame Builder Specification

> <details>

<!-- sdn-diagram:id=frame_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frame_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frame_builder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frame_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frame Builder Specification

## Scenarios

### frame_builder

#### frame_builder_new: passes is empty, current_pass is None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = frame_builder_new()
b.passes.len().to_equal(0)
b.current_pass.to_be_nil()
```

</details>

#### begin_render_pass: returns monotonic pass id (1, then 2)

1. var b = frame builder new
2. b end render pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = frame_builder_new()
val bounds = _rect(0.0, 0.0, 800.0, 600.0)
val id1 = b.begin_render_pass(bounds)
b.end_render_pass()
val id2 = b.begin_render_pass(bounds)
id1.to_equal(1)
id2.to_equal(2)
id2.to_be_greater_than(id1)
```

</details>

#### add_solid_color_quad: appends to current pass

1. var b = frame builder new
2. b begin render pass
3. b add solid color quad
4. b add solid color quad


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = frame_builder_new()
val bounds = _rect(0.0, 0.0, 100.0, 100.0)
b.begin_render_pass(bounds)
b.add_solid_color_quad(_rect(0.0, 0.0, 50.0, 50.0), _red())
b.add_solid_color_quad(_rect(50.0, 50.0, 100.0, 100.0), _red())
match b.current_pass:
    case Some(p):
        p.quads.len().to_equal(2)
    case None:
        (false).to_equal(true)
```

</details>

#### end_render_pass: moves current pass into passes

1. var b = frame builder new
2. b begin render pass
3. b add solid color quad
4. b end render pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = frame_builder_new()
val bounds = _rect(0.0, 0.0, 100.0, 100.0)
b.begin_render_pass(bounds)
b.add_solid_color_quad(_rect(0.0, 0.0, 10.0, 10.0), _red())
b.end_render_pass()
b.passes.len().to_equal(1)
b.current_pass.to_be_nil()
```

</details>

#### build: returns frame with all passes

1. var b = frame builder new
2. b begin render pass
3. b end render pass
4. b begin render pass
5. b end render pass
6. b begin render pass
7. b end render pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = frame_builder_new()
val bounds = _rect(0.0, 0.0, 100.0, 100.0)
b.begin_render_pass(bounds)
b.end_render_pass()
b.begin_render_pass(bounds)
b.end_render_pass()
b.begin_render_pass(bounds)
b.end_render_pass()
val frame = b.build()
frame.render_passes.len().to_equal(3)
```

</details>

#### build: root_pass_id is last begun pass id

1. var b = frame builder new
2. b end render pass
3. b end render pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = frame_builder_new()
val bounds = _rect(0.0, 0.0, 100.0, 100.0)
val id1 = b.begin_render_pass(bounds)
b.end_render_pass()
val id2 = b.begin_render_pass(bounds)
b.end_render_pass()
val frame = b.build()
frame.root_pass_id.to_equal(id2)
```

</details>

#### build with no passes returns empty frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = frame_builder_new()
val frame = b.build()
frame.render_passes.len().to_equal(0)
frame.root_pass_id.to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/frame_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- frame_builder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
