# Editor Sdn Graph Specification

> <details>

<!-- sdn-diagram:id=editor_sdn_graph_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_sdn_graph_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_sdn_graph_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_sdn_graph_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Sdn Graph Specification

## Scenarios

### editor SDN graph parser

#### parses graph metadata and css file

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse(graph_sample())
expect(graph.name).to_equal("login_flow")
expect(graph.direction).to_equal("right")
expect(graph.theme).to_equal("modern")
expect(graph.css_file).to_equal("./modern.css")
```

</details>

#### weaves @ css labels into matching nodes and edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse(graph_sample())
expect(graph.nodes[0].css).to_equal("person")
expect(graph.nodes[1].css).to_equal("card service")
expect(graph.nodes[2].css).to_equal("storage")
expect(graph.nodes[2].shape).to_equal("cylinder")
expect(graph.edges[0].css).to_equal("primary")
expect(graph.edges[2].css).to_equal("async dashed")
```

</details>

#### parses dense @ attachments directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: dense\nUser: User @person\nUser -> Auth: Login @primary")
expect(graph.nodes[0].css).to_equal("person")
expect(graph.edges[0].css).to_equal("primary")
expect(graph.edges[0].kind).to_equal("normal")
```

</details>

#### records css definitions and style rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse("graph: styled\ncss card:\n    fill: var(color.card)\n    stroke: var(color.line)\ncss primary:\n    target: edge\n    stroke_width: 2")
expect(graph.css_defs.len()).to_equal(2)
expect(graph.styles.len()).to_equal(3)
expect(graph.css_defs[1].target).to_equal("edge")
```

</details>

#### emits canonical SDN tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val canonical = sdn_graph_to_canonical_sdn(sdn_graph_parse(graph_sample()))
expect(canonical).to_contain("nodes |id, label, css, role, shape|")
expect(canonical).to_contain("edges |from, to, label, css, kind|")
expect(canonical).to_contain("User, User, person, actor,")
expect(canonical).to_contain("Auth, Log, Event, \"async dashed\", async")
```

</details>

### editor SDN graph integration

#### registers SDN graph as a built-in editor plugin

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/host.spl")
expect(src).to_contain("graph_language_manifest()")
val graph_src = read_text("src/lib/editor/extensions/builtin/graph_language.spl")
expect(graph_src).to_contain("sdn-graph-language")
expect(graph_src).to_contain("graph.render")
```

</details>

#### adapts fenced sdn-graph blocks into render blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```sdn-graph\n" + graph_sample() + "```")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("sdn_graph")
```

</details>

#### renders graph blocks in TUI preview

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```sdn-graph\n" + graph_sample() + "```")
val lines = md_render_blocks(model)
expect(lines[0]).to_contain("[graph: login_flow]")
expect(lines[1]).to_contain("User")
```

</details>

#### renders graph blocks as GUI HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 1, kind: "sdn_graph", from_line: 0, to_line: 4, content: graph_sample(), rendered_lines: ["```sdn-graph", graph_sample(), "```"], status: "ok")
val rendered = gui_render_markdown_block(block)
expect(rendered.html).to_contain("class=\"sdn-graph\"")
expect(rendered.html).to_contain("sdn-css-person")
expect(rendered.html).to_contain("data-css-file=\"./modern.css\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_sdn_graph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor SDN graph parser
- editor SDN graph integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
