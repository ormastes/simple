# Formatter Minimal Specification

> <details>

<!-- sdn-diagram:id=formatter_minimal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formatter_minimal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formatter_minimal_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formatter_minimal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Minimal Specification

## Scenarios

### FormatConfig minimal

#### creates config

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = FormatConfig(
    indent_size: 4,
    max_line_length: 100,
    use_tabs: false,
    blank_lines_between_items: 2,
    continuation_indent: 8
)
expect config.indent_size == 4
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter_minimal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FormatConfig minimal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
