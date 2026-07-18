# Lsp Result Panel Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=lsp_result_panel_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_result_panel_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_result_panel_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_result_panel_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Result Panel Numeric Guard Specification

## Scenarios

### editor LSP result panel numeric guard

#### guards serialized selection parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/editor/view/lsp_result_panel.spl") ?? ""

expect(source).to_contain("val sel = parts[1].to_int() ?? panel.selected")
expect(source.contains("val sel = parts[1].to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/lsp_result_panel_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor LSP result panel numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
