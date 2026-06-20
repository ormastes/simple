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
| 30 | 30 | 0 | 0 |

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

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: flow\nA: A\nB: B\nA -> B: submit @primary kind: action route: orthogonal waypoints: 10x20;80x20 start: right end: left")
expect(graph.edges.len()).to_equal(1)
expect(graph.edges[0].kind).to_equal("action")
expect(graph.edges[0].route).to_equal("orthogonal")
expect(graph.edges[0].waypoints).to_equal("10x20;80x20")
expect(graph.edges[0].start_anchor).to_equal("right")
expect(graph.edges[0].end_anchor).to_equal("left")
val labeled = sdn_graph_parse("graph: labels\nA: A\nB: B\nA -> B: note label_x: 42 label_y: -7\nB -> A: bad label_x: left label_y: 9px")
expect(labeled.edges[0].label_x).to_equal("42")
expect(labeled.edges[0].label_y).to_equal("-7")
expect(labeled.edges[1].label_x).to_equal("")
expect(labeled.edges[1].label_y).to_equal("")
```

</details>

#### parses draw canvas metadata from dense SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: canvas\ncanvas: width: 1200 height: 800 grid: 16 snap: true zoom: 125 background: #ffffff\nA: A")
expect(graph.canvas_width).to_equal("1200")
expect(graph.canvas_height).to_equal("800")
expect(graph.canvas_grid).to_equal("16")
expect(graph.canvas_snap).to_equal("true")
expect(graph.canvas_zoom).to_equal("125")
expect(graph.canvas_background).to_equal("#ffffff")
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

#### renders deterministic HTML editor metadata for the draw canvas

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: editor\ncanvas: width: 1200 height: 800 grid: 16 snap: true zoom: 125 background: #ffffff\nCard: Card x: 10 y: 20 width: 200 height: 100")
val html = sdn_graph_render_html(graph)
expect(html).to_contain("data-canvas-width=\"1200\"")
expect(html).to_contain("data-canvas-height=\"800\"")
expect(html).to_contain("data-canvas-grid=\"16\"")
expect(html).to_contain("data-canvas-snap=\"true\"")
expect(html).to_contain("data-canvas-zoom=\"125\"")
expect(html).to_contain("data-canvas-background=\"#ffffff\"")
expect(html).to_contain("style=\"width:1200px;height:800px;background-color:#ffffff")
expect(html).to_contain("background-size:16px 16px;")

val checked = sdn_graph_update_canvas_checked(graph, " 1440 ", " 960 ", " 24 ", " false ", " 150 ", " #f8fafc ")
expect(checked.accepted).to_be(true)
expect(checked.graph.canvas_width).to_equal("1440")
expect(checked.graph.canvas_snap).to_equal("false")
expect(checked.graph.canvas_background).to_equal("#f8fafc")
```

</details>

#### escapes draw canvas metadata in HTML attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_update_canvas(sdn_graph_parse("graph: escaped\nA: A"), "100", "80", "10", "true", "100", "\"<bg>&")
val html = sdn_graph_render_html(graph)
expect(html).to_contain("data-canvas-background=\"&quot;&lt;bg&gt;&amp;\"")
expect(html).to_contain("style=\"width:100px;height:80px;")
```

</details>

#### sanitizes whitespace-obfuscated SDD css_file URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: escaped\ncss_file: \"java\tscript:alert(1)\"\nA: A")
val html = sdn_graph_render_html(graph)
expect(html).to_contain("data-css-file=\"#\"")
```

</details>

#### sanitizes protocol-relative SDD css_file URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: escaped\ncss_file: \"//evil.example/diagram.css\"\nA: A")
val html = sdn_graph_render_html(graph)
expect(html).to_contain("data-css-file=\"#\"")
```

</details>

#### sanitizes legacy script and local file SDD css_file URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy = sdn_graph_render_html(sdn_graph_parse("graph: escaped\ncss_file: \"vbscript:msgbox(1)\"\nA: A"))
val local = sdn_graph_render_html(sdn_graph_parse("graph: escaped\ncss_file: \"file:///etc/passwd\"\nA: A"))
expect(legacy).to_contain("data-css-file=\"#\"")
expect(local).to_contain("data-css-file=\"#\"")
```

</details>

#### canonicalizes quoted SDD css_file values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: escaped\ncss_file: \"styles/diagram\"\"dark.css\"\nA: A")
val canon = sdn_graph_to_canonical_sdn(graph)
val parsed = sdn_graph_parse(canon)
expect(canon).to_contain("css_file: \"styles/diagram\"\"dark.css\"")
expect(parsed.css_file).to_equal("styles/diagram\"dark.css")
```

</details>

#### escapes node and edge labels in rendered SDD HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: escaped\nA: <Start> x: 10 y: 20 width: 80 height: 20\nB: <End> x: 220 y: 20 width: 80 height: 20\nA -> B: <flow> route: simple start: right end: left")
val html = sdn_graph_render_html(graph)
expect(html).to_contain("data-label=\"&lt;Start&gt;\"")
expect(html).to_contain(">&lt;Start&gt;</button>")
expect(html).to_contain("data-label=\"&lt;flow&gt;\"")
expect(html).to_contain(">&lt;flow&gt;</div>")
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

#### round-trips canonical table fields with commas and quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: flow\nA: Alpha \"One\", Inc x: 8 y: 12 width: 48 height: 48\nB: End x: 120 y: 12 width: 80 height: 48\nC: A|B\\C x: 10 y: 90 width: 48 height: 48\nA -> B: flow,fast route: simple waypoints: 56x36,80x36 start: right end: left")
val canon = sdn_graph_to_canonical_sdn(graph)
val parsed = sdn_graph_parse(canon)
expect(canon).to_contain("\"Alpha \"\"One\"\", Inc\"")
expect(canon).to_contain("C, \"A|B\\C\"")
expect(parsed.nodes[0].label).to_equal("Alpha \"One\", Inc")
expect(parsed.nodes[2].label).to_equal("A|B\\C")
expect(parsed.edges[0].label).to_equal("flow,fast")
expect(parsed.edges[0].waypoints).to_equal("56x36,80x36")
val bad_label_points = sdn_graph_parse("graph: bad\nnodes |id, label, css, role, shape, x, y, width, height, layer, parent|\n    A, A, , , , , , , , , \n    B, B, , , , , , , , , \nedges |from, to, label, css, kind, route, waypoints, start_anchor, end_anchor, label_x, label_y|\n    A, B, bad, , normal, simple, , , , 1px, nope")
expect(bad_label_points.edges[0].label_x).to_equal("")
expect(bad_label_points.edges[0].label_y).to_equal("")
val styled = sdn_graph_parse("graph: style\ncss fancy:\n    note: \"quoted\", value\n    title: A|B\\C\nA: Alpha @fancy")
val style_canon = sdn_graph_to_canonical_sdn(styled)
val reparsed_style = sdn_graph_parse(style_canon)
expect(style_canon).to_contain("fancy, note, \"\"\"quoted\"\", value\"")
expect(style_canon).to_contain("fancy, title, \"A|B\\C\"")
expect(sdn_graph_inspect_style_rule(reparsed_style, "fancy", "note").value).to_equal("\"quoted\", value")
expect(sdn_graph_inspect_style_rule(reparsed_style, "fancy", "title").value).to_equal("A|B\\C")
```

</details>

#### canonicalizes draw canvas metadata before graph tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: flow\ncanvas: width: 1024 height: 768 grid: 8 snap: false zoom: 90 background: transparent\nA: Start")
val canon = sdn_graph_to_canonical_sdn(graph)
expect(canon).to_contain("canvas: width: 1024 height: 768 grid: 8 snap: false zoom: 90 background: transparent")
expect(canon).to_contain("nodes |id, label, css, role, shape, x, y, width, height, layer, parent|")
```

</details>

#### weaves layout shape and parent edits into matching nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
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
val unsafe = sdn_graph_parse("graph: weave\nSvc: Service role: service x: 1 y: 2 width: 80 height: 40\nweave @:\n    node where role = service:\n        x: left\n        y: -10\n        width: -1\n        height: tall")
expect(unsafe.nodes[0].x).to_equal("1")
expect(unsafe.nodes[0].y).to_equal("-10")
expect(unsafe.nodes[0].width).to_equal("80")
expect(unsafe.nodes[0].height).to_equal("40")
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

#### renders transient selected node metadata without changing graph state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: select\nA: Alpha @plain role: box shape: rect x: 10 y: 20 width: 80 height: 20 layer: base\nB: Beta @target role: box shape: rounded x: 220 y: 20 width: 80 height: 20 layer: front\nA -> B: c route: simple start: right end: left")
val html = sdn_graph_render_html_with_selection(graph, "B", -1)
expect(html).to_contain("data-selected-node-id=\"B\"")
expect(html).to_contain("data-selected-edge-index=\"-1\"")
expect(html).to_contain("class=\"sdn-graph-node sdd-node sdn-css-target sdd-selected\"")
expect(html).to_contain("data-node=\"B\" data-selected=\"true\" aria-selected=\"true\"")
expect(sdn_graph_render_html(graph)).to_contain("data-selected-node-id=\"\"")
expect(graph.nodes[1].css).to_equal("target")
```

</details>

#### renders transient selected connector metadata and ignores invalid connector selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: select-edge\nA: Alpha x: 10 y: 20 width: 80 height: 20\nB: Beta x: 220 y: 20 width: 80 height: 20\nA -> B: c @primary route: simple start: right end: left")
val selected = sdn_graph_render_html_with_selection(graph, "", 0)
val invalid = sdn_graph_render_html_with_selection(graph, "", 99)
expect(selected).to_contain("data-selected-edge-index=\"0\"")
expect(selected).to_contain("class=\"sdd-connector-path sdn-css-primary sdd-selected\"")
expect(selected).to_contain("data-edge-index=\"0\" data-selected=\"true\" aria-selected=\"true\"")
expect(selected).to_contain("class=\"sdn-graph-edge sdd-connector sdn-css-primary sdd-selected\"")
expect(invalid).to_contain("data-selected-edge-index=\"-1\"")
expect(invalid).to_contain("data-edge-index=\"0\" data-selected=\"false\" aria-selected=\"false\"")
val invalid_node = sdn_graph_render_html_with_selection(graph, "Missing", -1)
expect(invalid_node).to_contain("data-selected-node-id=\"\"")
```

</details>

#### resolves inherited CSS style values

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: style\ncss base:\n    fill: #ffffff\n    stroke: #111111\ncss accent:\n    extends: base\n    fill: #eeeeee\nA: Alpha @accent")
expect(sdn_graph_resolved_style(graph, "accent", "node")).to_contain("background-color:#ffffff")
expect(sdn_graph_resolved_style(graph, "accent", "node")).to_contain("background-color:#eeeeee")
expect(sdn_graph_resolved_style_value(graph, "accent", "node", "fill")).to_equal("#eeeeee")
expect(sdn_graph_resolved_style_value(graph, "accent", "node", "stroke")).to_equal("#111111")

val checked = sdn_graph_set_style_rule_checked(graph, " accent ", " node ", " base ", " stroke ", " #222222 ")
expect(checked.accepted).to_be(true)
expect(sdn_graph_resolved_style_value(checked.graph, "accent", "node", "stroke")).to_equal("#222222")
expect(sdn_graph_inspect_style_rule(checked.graph, " accent ", " stroke ").value).to_equal("#222222")
val deleted = sdn_graph_delete_style_rule_checked(checked.graph, " accent ", " stroke ")
expect(deleted.accepted).to_be(true)
expect(sdn_graph_resolved_style_value(deleted.graph, "accent", "node", "stroke")).to_equal("#111111")
```

</details>

#### rejects unsafe SDD CSS function values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: style\ncss bad:\n    fill: expression(alert(1))\n    stroke: var(--safe-stroke)\nA: Alpha @bad")
val html = sdn_graph_render_html(graph)
expect(sdn_graph_resolved_style_value(graph, "bad", "node", "fill")).to_equal("")
expect(sdn_graph_resolved_style_value(graph, "bad", "node", "stroke")).to_equal("var(--safe-stroke)")
expect(html.contains("expression(alert(1))")).to_be(false)
expect(html).to_contain("border-color:var(--safe-stroke)")

val bad_token = sdn_graph_parse("graph: style\ncss bad;token:\n    fill: #ff0000\nA: Alpha @bad;token")
val bad_token_html = sdn_graph_render_html(bad_token)
expect(sdn_graph_resolved_style_value(bad_token, "bad;token", "node", "fill")).to_equal("")
expect(bad_token_html.contains("background-color:#ff0000")).to_be(false)
```

</details>

#### inspects selected nodes and connectors as pure snapshots

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: inspect\nA: Alpha @panel role: source shape: rounded x: 10 y: 20 width: 80 height: 20 layer: base parent: Group\nB: Beta x: 220 y: 20 width: 80 height: 20\nA -> B: c @primary kind: action route: orthogonal waypoints: 140x30;200x80 start: right end: left")
val node = sdn_graph_inspect_node(graph, "A")
val edge = sdn_graph_inspect_edge(graph, 0)
expect(node.found).to_be(true)
expect(node.reason).to_equal("selected")
expect(node.id).to_equal("A")
expect(node.css).to_equal("panel")
expect(node.role).to_equal("source")
expect(node.shape).to_equal("rounded")
expect(node.x).to_equal("10")
expect(node.parent).to_equal("Group")
expect(edge.found).to_be(true)
expect(edge.reason).to_equal("selected")
expect(edge.edge_index).to_equal(0)
expect(edge.from_id).to_equal("A")
expect(edge.to_id).to_equal("B")
expect(edge.css).to_equal("primary")
expect(edge.kind).to_equal("action")
expect(edge.route).to_equal("orthogonal")
expect(edge.waypoints).to_equal("140x30;200x80")
expect(edge.path).to_equal("M 90,30 L 140,30 L 200,30 L 200,80 L 220,80 L 220,30")
```

</details>

#### reports missing node and connector inspection targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: missing\nA: Alpha\nB: Beta\nA -> B: c")
val node = sdn_graph_inspect_node(graph, "Nope")
val edge = sdn_graph_inspect_edge(graph, -1)
expect(node.found).to_be(false)
expect(node.reason).to_equal("missing-node")
expect(node.id).to_equal("Nope")
expect(edge.found).to_be(false)
expect(edge.reason).to_equal("missing-edge")
expect(edge.edge_index).to_equal(-1)
```

</details>

#### updates edge routing through a pure edit operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: edit\nA: A x: 10 y: 20 width: 80 height: 20\nB: B x: 220 y: 20 width: 80 height: 20\nA -> B: c route: simple start: right end: left")
val updated = sdn_graph_update_edge_at(graph, 0, "orthogonal", "140x30;200x80", "right", "left")
val html = sdn_graph_render_html(updated)
expect(updated.edges[0].route).to_equal("orthogonal")
expect(updated.edges[0].waypoints).to_equal("140x30;200x80")
expect(html).to_contain("data-path=\"M 90,30 L 140,30 L 200,30 L 200,80 L 220,80 L 220,30\"")

val malformed = sdn_graph_parse("graph: edit\nA: A x: 10 y: 20 width: 80 height: 20\nB: B x: 220 y: 20 width: 80 height: 20\nA -> B: c route: orthogonal waypoints: 140x30;bad;200x80 start: right end: left")
val malformed_html = sdn_graph_render_html(malformed)
expect(malformed.edges[0].waypoints).to_equal("140x30;bad;200x80")
expect(malformed_html).to_contain("data-path=\"M 90,30 L 220,30\"")

val checked = sdn_graph_update_edge_checked(graph, 0, " orthogonal ", " 140x30;200x80 ", " right ", " left ")
expect(checked.accepted).to_be(true)
expect(checked.graph.edges[0].route).to_equal("orthogonal")
expect(checked.graph.edges[0].start_anchor).to_equal("right")

val added = sdn_graph_add_edge_checked(graph, " A ", " B ", "new", " primary ", " action ", " simple ", " 90x30 ", " right ", " left ")
expect(added.accepted).to_be(true)
expect(added.graph.edges[1].from_id).to_equal("A")
expect(added.graph.edges[1].css).to_equal("primary")

val endpoints = sdn_graph_update_edge_endpoints_checked(graph, 0, " B ", " A ")
expect(endpoints.accepted).to_be(true)
expect(endpoints.graph.edges[0].from_id).to_equal("B")
expect(sdn_graph_update_edge_endpoints_checked(graph, 0, "B", "A bad").reason).to_equal("invalid-id")

val styled = sdn_graph_update_edge_style_checked(graph, 0, " primary dashed ")
expect(styled.accepted).to_be(true)
expect(styled.graph.edges[0].css).to_equal("primary dashed")

val kinded = sdn_graph_update_edge_kind_checked(graph, 0, " async ")
expect(kinded.accepted).to_be(true)
expect(kinded.graph.edges[0].kind).to_equal("async")
```

</details>

#### updates canvas metadata through a pure edit operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: edit-canvas\ncanvas: width: 800 height: 600 grid: 10 snap: false zoom: 100 background: white\nA: A x: 10 y: 20 width: 80 height: 20\nB: B x: 220 y: 20 width: 80 height: 20\nA -> B: c route: simple start: right end: left")
val updated = sdn_graph_update_canvas(graph, "1440", "960", "24", "true", "150", "#f8fafc")
val html = sdn_graph_render_html(updated)
expect(updated.canvas_width).to_equal("1440")
expect(updated.canvas_height).to_equal("960")
expect(updated.canvas_grid).to_equal("24")
expect(updated.canvas_snap).to_equal("true")
expect(updated.canvas_zoom).to_equal("150")
expect(updated.canvas_background).to_equal("#f8fafc")
expect(updated.nodes[0].id).to_equal("A")
expect(updated.edges[0].from_id).to_equal("A")
expect(html).to_contain("data-canvas-width=\"1440\"")
expect(html).to_contain("data-canvas-grid=\"24\"")
```

</details>

#### updates node shape style and geometry through a pure edit operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
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

val checked_shape = sdn_graph_update_node_shape_checked(graph, 0, " diamond ")
expect(checked_shape.accepted).to_be(true)
expect(checked_shape.graph.nodes[0].shape).to_equal("diamond")
val checked_style = sdn_graph_update_node_style_checked(checked_shape.graph, 0, " primary selected ")
expect(checked_style.accepted).to_be(true)
expect(checked_style.graph.nodes[0].css).to_equal("primary selected")
expect(sdn_graph_update_node_shape_checked(graph, 0, "bad shape").reason).to_equal("invalid-shape-token")
expect(sdn_graph_update_node_style_checked(graph, 0, "primary bad\"onclick=1").reason).to_equal("invalid-style-token")

val added = sdn_graph_add_node_checked(graph, "C", "Choice", "accent", "decision", "diamond", " 80 ", " 80 ", "64", "48", "front", "")
expect(added.accepted).to_be(true)
expect(added.graph.nodes[2].x).to_equal("80")
expect(added.graph.nodes[2].y).to_equal("80")
expect(sdn_graph_add_node_checked(graph, "bad id", "Bad", "", "", "", "80", "80", "64", "48", "", "").reason).to_equal("invalid-id")

val copied = sdn_graph_duplicate_node_checked(graph, " A ", " A_copy ", " 12 ", " 8 ")
expect(copied.accepted).to_be(true)
expect(copied.graph.nodes[1].id).to_equal("A_copy")
expect(copied.graph.nodes[1].x).to_equal("22")
expect(sdn_graph_duplicate_node_checked(graph, "A", "bad id", "1", "1").reason).to_equal("invalid-id")

val invalid_add = sdn_graph_add_node_checked(graph, "D", "Bad", "accent", "decision", "diamond", "left", "80", "-1", "48", "front", "")
expect(invalid_add.accepted).to_be(false)
expect(invalid_add.reason).to_equal("invalid-geometry")
expect(invalid_add.graph.nodes.len()).to_equal(2)
```

</details>

#### preserves group membership through tables and pure parent edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
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

val checked_parent = sdn_graph_update_node_parent_checked(ungrouped, " Child ", " Container ")
expect(checked_parent.accepted).to_be(true)
expect(checked_parent.graph.nodes[1].parent).to_equal("Container")
expect(sdn_graph_update_node_parent_checked(graph, "Child bad", "Container").reason).to_equal("invalid-id")

val ordered = sdn_graph_reorder_node_checked(graph, " Child ", " back ")
expect(ordered.accepted).to_be(true)
expect(ordered.graph.nodes[0].id).to_equal("Child")
```

</details>

#### aligns selected SDD nodes with guarded geometry signatures

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: align\nA: A x: 10 y: 20 width: 30 height: 20\nB: B x: 80 y: 40 width: 20 height: 20\nC: C x: 150 y: 80 width: 30 height: 20")
val ids = ["A", "B", "C"]
val signature = sdn_graph_geometry_signature(graph, ids)
expect(signature).to_equal("A:10,20,30,20;B:80,40,20,20;C:150,80,30,20")

val left = sdn_graph_align_checked(graph, ids, signature, "left")
expect(left.accepted).to_be(true)
expect(left.reason).to_equal("updated")
expect(left.graph.nodes[0].x).to_equal("10")
expect(left.graph.nodes[1].x).to_equal("10")
expect(left.graph.nodes[2].x).to_equal("10")
expect(left.diff).to_contain("@@ sdd-align left @@")

val middle = sdn_graph_align_checked(graph, ids, signature, "middle")
expect(middle.accepted).to_be(true)
expect(middle.graph.nodes[0].y).to_equal("50")
expect(middle.graph.nodes[1].y).to_equal("50")
expect(middle.graph.nodes[2].y).to_equal("50")

val stale = sdn_graph_align_checked(graph, ids, "A:0,0,1,1", "left")
expect(stale.accepted).to_be(false)
expect(stale.reason).to_equal("stale-selection")

val missing = sdn_graph_align_checked(graph, ["A", "Missing"], sdn_graph_geometry_signature(graph, ["A", "Missing"]), "left")
expect(missing.accepted).to_be(false)
expect(missing.reason).to_equal("missing-node")

val unsupported = sdn_graph_align_checked(graph, ids, signature, "diagonal")
expect(unsupported.accepted).to_be(false)
expect(unsupported.reason).to_equal("unsupported-align-mode")
```

</details>

#### distributes selected SDD nodes with guarded geometry signatures

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: distribute\nB: B x: 120 y: 120 width: 20 height: 20\nA: A x: 0 y: 0 width: 20 height: 20\nC: C x: 20 y: 20 width: 20 height: 20")
val ids = ["A", "B", "C"]
val signature = sdn_graph_geometry_signature(graph, ids)
val horizontal = sdn_graph_distribute_checked(graph, ids, signature, "horizontal")
expect(horizontal.accepted).to_be(true)
expect(horizontal.reason).to_equal("updated")
expect(horizontal.graph.nodes[0].x).to_equal("120")
expect(horizontal.graph.nodes[1].x).to_equal("0")
expect(horizontal.graph.nodes[2].x).to_equal("60")
expect(horizontal.graph.nodes[2].y).to_equal("20")
expect(sdn_graph_to_canonical_sdn(horizontal.graph)).to_contain("C, C, , , , 60, 20, 20, 20")

val vertical = sdn_graph_distribute_checked(graph, ids, signature, "vertical")
expect(vertical.accepted).to_be(true)
expect(vertical.graph.nodes[2].y).to_equal("60")

val too_few = sdn_graph_distribute_checked(graph, ["A", "B"], sdn_graph_geometry_signature(graph, ["A", "B"]), "horizontal")
expect(too_few.accepted).to_be(false)
expect(too_few.reason).to_equal("invalid-selection")

val invalid = sdn_graph_parse("graph: invalid\nA: A x: left y: 0 width: 20 height: 20\nB: B x: 20 y: 20 width: 20 height: 20\nC: C x: 120 y: 120 width: 20 height: 20")
val invalid_result = sdn_graph_distribute_checked(invalid, ids, sdn_graph_geometry_signature(invalid, ids), "horizontal")
expect(invalid_result.accepted).to_be(false)
expect(invalid_result.reason).to_equal("invalid-geometry")

val unsupported = sdn_graph_distribute_checked(graph, ids, signature, "diagonal")
expect(unsupported.accepted).to_be(false)
expect(unsupported.reason).to_equal("unsupported-distribute-axis")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/sdd_diagram_editor.md](doc/02_requirements/feature/sdd_diagram_editor.md)
- **Plan:** [doc/03_plan/sys_test/sdd_diagram_editor.md](doc/03_plan/sys_test/sdd_diagram_editor.md)
- **Design:** [doc/07_guide/lib/api/sdn_graph.md](doc/07_guide/lib/api/sdn_graph.md)
- **Research:** [doc/01_research/local/sdd_diagram_editor.md](doc/01_research/local/sdd_diagram_editor.md)


</details>
