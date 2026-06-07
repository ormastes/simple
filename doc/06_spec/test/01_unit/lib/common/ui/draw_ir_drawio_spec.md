# Draw Ir Drawio Specification

> <details>

<!-- sdn-diagram:id=draw_ir_drawio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_drawio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_drawio_spec -> std
draw_ir_drawio_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_drawio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Drawio Specification

## Scenarios

### Draw IR Draw.io mxGraph skin

#### imports a Draw.io fixture into Draw IR boxes and edges

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = mxgraph_to_draw_ir(_drawio_fixture())
val commands = composition.batches[0].commands

expect(composition.schema).to_equal("simple-draw-ir-v2")
expect(commands.len()).to_equal(3)
expect(commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(commands[0].component_id).to_equal("box-a")
expect(commands[0].parent_id).to_equal("1")
expect(commands[0].x).to_equal(20)
expect(commands[0].y).to_equal(30)
expect(commands[0].width).to_equal(120)
expect(commands[0].height).to_equal(60)
expect(commands[0].computed_style[0].key).to_equal("rounded")
expect(commands[0].computed_style[1].value).to_equal("#dae8fc")
expect(commands[2].kind).to_equal(DRAW_IR_COMMAND_EDGE)
expect(commands[2].edge.source).to_equal("box-a")
expect(commands[2].edge.target).to_equal("box-b")
expect(commands[2].edge.routing).to_equal(DRAW_IR_EDGE_ORTHOGONAL)
expect(commands[2].edge.style[1].key).to_equal("strokeColor")
```

</details>

#### exports and re-imports box edge geometry and style identity

1. draw ir batch
   - Expected: commands.len() equals `3`
   - Expected: commands[0].component_id equals `box-a`
   - Expected: commands[0].x equals `20`
   - Expected: commands[0].width equals `120`
   - Expected: commands[0].computed_style[1].value equals `#dae8fc`
   - Expected: commands[2].component_id equals `edge-a-b`
   - Expected: commands[2].edge.source equals `box-a`
   - Expected: commands[2].edge.target equals `box-b`
   - Expected: commands[2].edge.style[0].value equals `block`


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface", "root", 0, 0, 400, 160, 0, 1000, false)
val imported = mxgraph_to_draw_ir(_drawio_fixture())
val composition = draw_ir_composition("diagram", "scene-1", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("diagram-batch", DRAW_IR_BACKEND_CPU, embedding, imported.batches[0].commands)
])

val mxgraph = draw_ir_to_mxgraph(composition)
val reparsed = mxgraph_to_draw_ir(mxgraph)
val commands = reparsed.batches[0].commands

expect(mxgraph).to_contain("<mxGraphModel")
expect(mxgraph).to_contain("id=\"box-a\"")
expect(mxgraph).to_contain("source=\"box-a\" target=\"box-b\" edge=\"1\"")
expect(commands.len()).to_equal(3)
expect(commands[0].component_id).to_equal("box-a")
expect(commands[0].x).to_equal(20)
expect(commands[0].width).to_equal(120)
expect(commands[0].computed_style[1].value).to_equal("#dae8fc")
expect(commands[2].component_id).to_equal("edge-a-b")
expect(commands[2].edge.source).to_equal("box-a")
expect(commands[2].edge.target).to_equal("box-b")
expect(commands[2].edge.style[0].value).to_equal("block")
```

</details>

#### exports hand-built Draw IR edge commands as mxGraph edges

1. [draw ir style prop

2. draw ir embedding config

3. [draw ir edge command


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edge = draw_edge(
    "edge-manual",
    "node-a",
    "node-b",
    DRAW_IR_EDGE_ORTHOGONAL,
    [],
    [draw_ir_style_prop("endArrow", "block")]
)
val composition = draw_ir_composition("diagram", "scene-2", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch(
        "manual",
        DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config("surface", "root", 0, 0, 200, 100, 0, 1000, false),
        [draw_ir_edge_command(edge)]
    )
])

val mxgraph = draw_ir_to_mxgraph(composition)

expect(mxgraph).to_contain("id=\"edge-manual\"")
expect(mxgraph).to_contain("source=\"node-a\"")
expect(mxgraph).to_contain("target=\"node-b\"")
expect(mxgraph).to_contain("edge=\"1\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Draw IR Draw.io mxGraph skin

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
