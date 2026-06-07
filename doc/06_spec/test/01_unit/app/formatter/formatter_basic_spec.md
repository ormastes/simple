# Formatter Basic Specification

> <details>

<!-- sdn-diagram:id=formatter_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formatter_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formatter_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formatter_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Basic Specification

## Scenarios

### Formatter Basic

#### keeps query formatting input sanitization before formatting

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/query_formatting.spl") ?? ""

expect(source).to_contain("val clean_file = sanitize_path(file)")
expect(source).to_contain("if clean_file == \"\":")
expect(source).to_contain("Formatting failed for: {clean_file}")
```

</details>

#### keeps JSON stats formatter entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/stats/json_formatter.spl") ?? ""

expect(source).to_contain("fn format_json(")
expect(source).to_contain("fn format_doc_coverage_json(stats: DocCoverageStats) -> text")
expect(source).to_contain("fn format_enhanced_json(")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter/formatter_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Formatter Basic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
