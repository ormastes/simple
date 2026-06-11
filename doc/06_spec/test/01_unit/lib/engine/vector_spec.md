# vector_spec

> Engine Vector Renderer — VectorRenderer command emission tests

<!-- sdn-diagram:id=vector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vector_spec

Engine Vector Renderer — VectorRenderer command emission tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/vector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Vector Renderer — VectorRenderer command emission tests

Tests that shape helper methods push the correct number of render
commands into the command buffer.

## Scenarios

### VectorRenderer

#### create works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
val tol_i = vr.tolerance.value * 1000.0
expect(tol_i).to_be_greater_than(99.0)
expect(tol_i).to_be_less_than(101.0)
```

</details>

#### fill_rect pushes 1 command

1. var cmds = RenderCommandBuffer create
2. vr fill rect
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
val rect = Rect2.new(0.0, 0.0, 100.0, 50.0)
vr.fill_rect(cmds, rect, EngineColor.red(), ZIndex(value: 0))
expect(cmds.len()).to_equal(1)
```

</details>

#### fill_circle pushes 1 command

1. var cmds = RenderCommandBuffer create
2. vr fill circle
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
vr.fill_circle(cmds, 100.0, 100.0, 50.0, EngineColor.blue(), ZIndex(value: 0))
expect(cmds.len()).to_equal(1)
```

</details>

#### stroke_rect pushes 4 commands

1. var cmds = RenderCommandBuffer create
2. vr stroke rect
   - Expected: cmds.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
val rect = Rect2.new(10.0, 10.0, 100.0, 80.0)
vr.stroke_rect(cmds, rect, 2.0, EngineColor.white(), ZIndex(value: 0))
# stroke_rect emits 4 fill_rect calls (top, bottom, left, right)
expect(cmds.len()).to_equal(4)
```

</details>

#### stroke_line pushes 1 command

1. var cmds = RenderCommandBuffer create
2. vr stroke line
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
vr.stroke_line(cmds, 0.0, 0.0, 100.0, 100.0, 2.0, EngineColor.green(), ZIndex(value: 0))
expect(cmds.len()).to_equal(1)
```

</details>

#### multiple calls accumulate in buffer

1. var cmds = RenderCommandBuffer create
2. vr fill rect
3. vr fill circle
4. vr stroke line
   - Expected: cmds.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
val rect = Rect2.new(0.0, 0.0, 50.0, 50.0)
vr.fill_rect(cmds, rect, EngineColor.red(), ZIndex(value: 0))
vr.fill_circle(cmds, 25.0, 25.0, 10.0, EngineColor.blue(), ZIndex(value: 1))
vr.stroke_line(cmds, 0.0, 0.0, 50.0, 50.0, 1.0, EngineColor.white(), ZIndex(value: 2))
expect(cmds.len()).to_equal(3)
```

</details>

#### stroke_rect with zero width pushes 0 commands

1. var cmds = RenderCommandBuffer create
2. vr stroke rect
   - Expected: cmds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vr = VectorRenderer.create()
var cmds = RenderCommandBuffer.create()
val rect = Rect2.new(10.0, 10.0, 100.0, 80.0)
vr.stroke_rect(cmds, rect, 0.0, EngineColor.white(), ZIndex(value: 0))
expect(cmds.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
