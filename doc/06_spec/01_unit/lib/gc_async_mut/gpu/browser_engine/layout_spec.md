# Layout Specification

> <details>

<!-- sdn-diagram:id=layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Specification

## Scenarios

### Browser engine layout traversal

#### lays out child boxes in source order and accumulates height

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _root([_text(2, "hello"), _text(3, "world")])
val layout = layout_tree(root, 200.0, 100.0)
val children = layout_get_children(layout)

expect(children.len()).to_equal(2)
expect(children[0].text_content).to_equal("hello")
expect(children[1].text_content).to_equal("world")
expect(layout_get_height(layout)).to_equal(30.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser engine layout traversal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
