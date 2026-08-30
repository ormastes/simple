# Lsp Query Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=lsp_query_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_query_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_query_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_query_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Query Numeric Guard Specification

## Scenarios

### lsp query numeric guard

#### defaults malformed line and column arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/lsp/lsp_query.spl") ?? ""

expect(source).to_contain("val line_num = args[2].to_int() ?? 0")
expect(source).to_contain("col = args[3].to_int() ?? 0")
expect(source.contains("val line_num = args[2].to_int()\n")).to_equal(false)
expect(source.contains("col = args[3].to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/lsp/lsp_query_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lsp query numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
