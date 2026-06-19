# sdn_graph_diagram_spec

> Verifies the SDN-backed diagram dialect used by Markdown docs and the IDE preview. SDD means Simple Diagram Document: a named SDN dialect that extends older relationship-only graph blocks with draw.io/Figma-style geometry, layers, parent/group membership, shapes, connector routing, anchors, and waypoints.

<!-- sdn-diagram:id=sdn_graph_diagram_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_graph_diagram_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_graph_diagram_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_graph_diagram_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sdn_graph_diagram_spec

Verifies the SDN-backed diagram dialect used by Markdown docs and the IDE preview. SDD means Simple Diagram Document: a named SDN dialect that extends older relationship-only graph blocks with draw.io/Figma-style geometry, layers, parent/group membership, shapes, connector routing, anchors, and waypoints.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/sdd_diagram_editor.md |
| Plan | doc/03_plan/sys_test/sdd_diagram_editor.md |
| Design | doc/07_guide/lib/api/sdn_graph.md |
| Research | doc/01_research/local/sdd_diagram_editor.md |
| Source | `test/01_unit/editor/services/sdn_graph_diagram_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the SDN-backed diagram dialect used by Markdown docs and the IDE
preview. SDD means Simple Diagram Document: a named SDN dialect that extends
older relationship-only graph blocks with draw.io/Figma-style geometry,
layers, parent/group membership, shapes, connector routing, anchors, and
waypoints.

## Examples

`Card: Card @panel shape: rounded x: 10 y: 20 width: 200 height: 100 layer: base`
creates a positioned diagram node. `Card -> Action: opens route: orthogonal
waypoints: 20x40;40x40 start: bottom end: left` creates an editable connector.

**Requirements:** doc/02_requirements/feature/sdd_diagram_editor.md
**NFR:** doc/02_requirements/nfr/sdd_diagram_editor.md
**Plan:** doc/03_plan/sys_test/sdd_diagram_editor.md
**Design:** doc/07_guide/lib/api/sdn_graph.md
**Research:** doc/01_research/local/sdd_diagram_editor.md
**Domain Research:** doc/01_research/domain/sdd_diagram_editor.md

## Scenarios

### SDD diagram document format

#### exposes a stable format name and file extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sdn_graph_format_name()).to_equal("SDD: Simple Diagram Document")
expect(sdn_graph_file_extension()).to_equal(".sdd.sdn")
```

</details>

#### parses explicit node geometry layer and shape from dense SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: editor\nFrame: Canvas @frame role: container shape: frame x: 12 y: 24 width: 320 height: 180 layer: base\nWidget: Button @component role: control shape: rounded x: 48 y: 80 width: 120 height: 40 layer: controls parent: Frame")
expect(graph.nodes.len()).to_equal(2)
expect(graph.nodes[0].id).to_equal("Frame")
expect(graph.nodes[0].shape).to_equal("frame")
expect(graph.nodes[0].x).to_equal("12")
expect(graph.nodes[0].y).to_equal("24")
expect(graph.nodes[0].width).to_equal("320")
expect(graph.nodes[0].height).to_equal("180")
expect(graph.nodes[0].layer).to_equal("base")
expect(graph.nodes[1].shape).to_equal("rounded")
expect(graph.nodes[1].layer).to_equal("controls")
expect(graph.nodes[1].parent).to_equal("Frame")
```

</details>

#### parses connector routes anchors and waypoints from dense SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: flow\nA: A\nB: B\nA -> B: submit @primary kind: action route: orthogonal waypoints: 10x20;80x20 start: right end: left")
expect(graph.edges.len()).to_equal(1)
expect(graph.edges[0].kind).to_equal("action")
expect(graph.edges[0].route).to_equal("orthogonal")
expect(graph.edges[0].waypoints).to_equal("10x20;80x20")
expect(graph.edges[0].start_anchor).to_equal("right")
expect(graph.edges[0].end_anchor).to_equal("left")
```

</details>

#### renders deterministic HTML editor metadata for geometry and connectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: editor\nCard: Card @panel shape: rounded x: 10 y: 20 width: 200 height: 100 layer: base\nAction: Action @button shape: pill x: 40 y: 60 width: 80 height: 28 layer: controls parent: Card\nCard -> Action: opens route: orthogonal waypoints: 20x40;40x40 start: bottom end: left")
val html = sdn_graph_render_html(graph)
expect(html).to_contain("class=\"sdn-graph sdd-diagram\"")
expect(html).to_contain("data-format=\"sdd\"")
expect(html).to_contain("data-format-name=\"SDD: Simple Diagram Document\"")
expect(html).to_contain("class=\"sdn-graph-node sdd-node sdn-css-panel\"")
expect(html).to_contain("data-layer=\"base\"")
expect(html).to_contain("data-parent=\"Card\"")
expect(html).to_contain("style=\"left:10px;top:20px;width:200px;height:100px\"")
expect(html).to_contain("class=\"sdd-connector-layer\"")
expect(html).to_contain("class=\"sdd-connector-path \"")
expect(html).to_contain("data-edge-index=\"0\"")
expect(html).to_contain("data-path=\"M 110,120 L 20,120 L 20,40 L 40,40 L 40,74\"")
expect(html).to_contain("d=\"M 110,120 L 20,120 L 20,40 L 40,40 L 40,74\"")
expect(html).to_contain("class=\"sdn-graph-edge sdd-connector")
expect(html).to_contain("data-route=\"orthogonal\"")
expect(html).to_contain("data-waypoints=\"20x40;40x40\"")
expect(html).to_contain("data-start-anchor=\"bottom\"")
expect(html).to_contain("data-end-anchor=\"left\"")
```

</details>

#### canonicalizes geometry and connector route tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: flow\nA: Start @start shape: circle x: 8 y: 12 width: 48 height: 48 layer: base\nB: End @end shape: terminator x: 120 y: 12 width: 80 height: 48 layer: base\nA -> B: done route: simple waypoints: 56x36 start: right end: left")
val canon = sdn_graph_to_canonical_sdn(graph)
expect(canon).to_contain("nodes |id, label, css, role, shape, x, y, width, height, layer, parent|")
expect(canon).to_contain("A, Start, start, , circle, 8, 12, 48, 48, base, ")
expect(canon).to_contain("edges |from, to, label, css, kind, route, waypoints, start_anchor, end_anchor|")
expect(canon).to_contain("A, B, done, , normal, simple, 56x36, right, left")
```

</details>

#### weaves layout shape and parent edits into matching nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: weave\nGroup: Services role: group\nSvc: Service role: service\nDB: Database role: database\nweave @:\n    node where role = service:\n        add: card\n        shape: rounded\n        x: 20\n        y: 30\n        width: 160\n        height: 70\n        layer: services\n        parent: Group")
expect(graph.nodes[1].css).to_equal("card")
expect(graph.nodes[1].shape).to_equal("rounded")
expect(graph.nodes[1].x).to_equal("20")
expect(graph.nodes[1].y).to_equal("30")
expect(graph.nodes[1].width).to_equal("160")
expect(graph.nodes[1].height).to_equal("70")
expect(graph.nodes[1].layer).to_equal("services")
expect(graph.nodes[1].parent).to_equal("Group")
expect(graph.nodes[2].shape).to_equal("")
```

</details>

#### renders orthogonal connector paths from anchors and waypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: route\nA: A x: 10 y: 20 width: 80 height: 20\nB: B x: 220 y: 20 width: 80 height: 20\nA -> B: c route: orthogonal waypoints: 140x30;200x80 start: right end: left")
val path = sdn_graph_render_edge_path(graph.edges[0], graph.nodes[0], graph.nodes[1])
val html = sdn_graph_render_html(graph)
expect(path).to_equal("M 90,30 L 140,30 L 200,30 L 200,80 L 220,80 L 220,30")
expect(html).to_contain("data-edge-index=\"0\"")
expect(html).to_contain("data-path=\"M 90,30 L 140,30 L 200,30 L 200,80 L 220,80 L 220,30\"")
expect(html).to_contain("data-waypoints=\"140x30;200x80\"")
```

</details>

#### defaults to straight connector paths for simple routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: simple\nA: A x: 10 y: 20 width: 80 height: 20\nB: B x: 220 y: 20 width: 80 height: 20\nA -> B: c route: simple start: right end: left")
expect(sdn_graph_render_edge_path(graph.edges[0], graph.nodes[0], graph.nodes[1])).to_equal("M 90,30 L 220,30")
```

</details>

#### updates edge routing through a pure edit operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: edit\nA: A x: 10 y: 20 width: 80 height: 20\nB: B x: 220 y: 20 width: 80 height: 20\nA -> B: c route: simple start: right end: left")
val updated = sdn_graph_update_edge_at(graph, 0, "orthogonal", "140x30;200x80", "right", "left")
val html = sdn_graph_render_html(updated)
expect(updated.edges[0].route).to_equal("orthogonal")
expect(updated.edges[0].waypoints).to_equal("140x30;200x80")
expect(html).to_contain("data-path=\"M 90,30 L 140,30 L 200,30 L 200,80 L 220,80 L 220,30\"")
```

</details>

#### updates node shape style and geometry through a pure edit operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: edit-node\nA: Alpha @plain role: box shape: rect x: 10 y: 20 width: 80 height: 20 layer: base\nB: Beta @plain role: box shape: rect x: 220 y: 20 width: 80 height: 20 layer: base\nA -> B: c route: simple start: right end: left")
val updated = sdn_graph_update_node_at(graph, 0, "accent selected", "decision", "diamond", "32", "48", "96", "64", "foreground")
val html = sdn_graph_render_html(updated)
val canon = sdn_graph_to_canonical_sdn(updated)
expect(updated.nodes[0].css).to_equal("accent selected")
expect(updated.nodes[0].role).to_equal("decision")
expect(updated.nodes[0].shape).to_equal("diamond")
expect(updated.nodes[0].x).to_equal("32")
expect(updated.nodes[0].y).to_equal("48")
expect(updated.nodes[0].width).to_equal("96")
expect(updated.nodes[0].height).to_equal("64")
expect(updated.nodes[0].layer).to_equal("foreground")
expect(updated.nodes[1].shape).to_equal("rect")
expect(updated.edges[0].from_id).to_equal("A")
expect(html).to_contain("class=\"sdn-graph-node sdd-node sdn-css-accent sdn-css-selected\"")
expect(html).to_contain("data-shape=\"diamond\"")
expect(html).to_contain("style=\"left:32px;top:48px;width:96px;height:64px\"")
expect(canon).to_contain("A, Alpha, \"accent selected\", decision, diamond, 32, 48, 96, 64, foreground")

val shaped = sdn_graph_update_node_shape_at(graph, 1, "cylinder")
val styled = sdn_graph_update_node_style_at(shaped, 1, "storage highlight")
expect(styled.nodes[1].shape).to_equal("cylinder")
expect(styled.nodes[1].css).to_equal("storage highlight")
expect(styled.nodes[1].x).to_equal("220")
expect(sdn_graph_render_html(styled)).to_contain("sdn-css-storage sdn-css-highlight")
```

</details>

#### preserves group membership through tables and pure parent edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: groups\nnodes |id, label, css, role, shape, x, y, width, height, layer, parent|\n    Container, Container, panel, group, frame, 0, 0, 220, 140, base, \n    Child, Child, primary, control, rounded, 20, 24, 80, 30, controls, Container")
expect(graph.nodes.len()).to_equal(2)
expect(graph.nodes[0].parent).to_equal("")
expect(graph.nodes[1].parent).to_equal("Container")
expect(sdn_graph_render_html(graph)).to_contain("data-parent=\"Container\"")
expect(sdn_graph_to_canonical_sdn(graph)).to_contain("Child, Child, primary, control, rounded, 20, 24, 80, 30, controls, Container")

val ungrouped = sdn_graph_update_node_parent_at(graph, 1, "")
expect(ungrouped.nodes[1].parent).to_equal("")
expect(ungrouped.nodes[1].x).to_equal("20")
expect(ungrouped.nodes[0].id).to_equal("Container")

val regrouped = sdn_graph_update_node_parent_at(ungrouped, 1, "Container")
expect(regrouped.nodes[1].parent).to_equal("Container")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/sdd_diagram_editor.md](doc/02_requirements/feature/sdd_diagram_editor.md)
- **Plan:** [doc/03_plan/sys_test/sdd_diagram_editor.md](doc/03_plan/sys_test/sdd_diagram_editor.md)
- **Design:** [doc/07_guide/lib/api/sdn_graph.md](doc/07_guide/lib/api/sdn_graph.md)
- **Research:** [doc/01_research/local/sdd_diagram_editor.md](doc/01_research/local/sdd_diagram_editor.md)


</details>
