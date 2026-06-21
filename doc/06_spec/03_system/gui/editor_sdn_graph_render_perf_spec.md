# Editor Sdn Graph Render Perf Specification

> <details>

<!-- sdn-diagram:id=editor_sdn_graph_render_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_sdn_graph_render_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_sdn_graph_render_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_sdn_graph_render_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Sdn Graph Render Perf Specification

## Scenarios

### SDN graph render hot path

#### renders larger graph text to HTML with all woven CSS labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = sdn_graph_parse(perf_graph_sample(64))
val html = sdn_graph_render_html(graph)
expect(graph.nodes.len()).to_equal(64)
expect(graph.edges.len()).to_equal(63)
expect(html).to_contain("data-graph=\"perf_preview\"")
expect(html).to_contain("data-node=\"N63\"")
expect(html).to_contain("sdn-css-card")
expect(html).to_contain("sdn-css-storage")
expect(html).to_contain("sdn-css-primary")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_sdn_graph_render_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN graph render hot path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
