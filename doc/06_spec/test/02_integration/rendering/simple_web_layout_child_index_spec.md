# Simple Web Layout Child Index Specification

> <details>

<!-- sdn-diagram:id=simple_web_layout_child_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_layout_child_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_layout_child_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_layout_child_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Layout Child Index Specification

## Scenarios

### simple web layout child index

#### keeps flat sibling block order stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _flat_rows(8)
val y0 = simple_web_layout_debug_layout_by_id(html, 200, 200, "row0", "y").to_i32()
val y1 = simple_web_layout_debug_layout_by_id(html, 200, 200, "row1", "y").to_i32()
val y7 = simple_web_layout_debug_layout_by_id(html, 200, 200, "row7", "y").to_i32()
expect(y1).to_be_greater_than(y0)
expect(y7).to_be_greater_than(y1)
```

</details>

#### renders a sibling-heavy startup fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _flat_rows(80)
val pixels = simple_web_layout_render_html_software_pixels(html, 160, 120)
expect(pixels.len()).to_equal(19200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_layout_child_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple web layout child index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
