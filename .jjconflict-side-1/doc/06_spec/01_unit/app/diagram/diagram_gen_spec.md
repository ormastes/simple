# Diagram Gen Specification

> <details>

<!-- sdn-diagram:id=diagram_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagram_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagram_gen_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagram_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagram Gen Specification

## Scenarios

### Diagram Gen

#### keeps diagram CLI and render adapter available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val main_source = rt_file_read_text("src/app/diagram/main.spl") ?? ""
val render_source = rt_file_read_text("src/app/diagram/render_adapter.spl") ?? ""

expect(main_source).to_contain("fn main() -> i64")
expect(render_source).to_contain("fn render_diagram(config: RenderConfig, events: [ProfileEvent]) -> RenderResult")
expect(render_source).to_contain("fn render_text(events: [ProfileEvent], mode: text) -> text")
expect(render_source).to_contain("fn render_html(events: [ProfileEvent], mode: text, config: RenderConfig) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/diagram/diagram_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Diagram Gen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
