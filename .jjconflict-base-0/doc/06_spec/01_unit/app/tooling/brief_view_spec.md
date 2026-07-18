# Brief View Specification

> <details>

<!-- sdn-diagram:id=brief_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=brief_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

brief_view_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=brief_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Brief View Specification

## Scenarios

### Brief View

#### keeps brief command parsing and formatting helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/brief/main.spl") ?? ""

expect(source).to_contain("fn count_lines(content: text) -> i64")
expect(source).to_contain("fn extract_signatures(content: text) -> [text]")
expect(source).to_contain("fn brief_format_size(bytes: i64) -> text")
expect(source).to_contain("fn main() -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/brief_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Brief View

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
