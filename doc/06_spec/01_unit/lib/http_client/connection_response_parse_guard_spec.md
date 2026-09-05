# Connection Response Parse Guard Specification

> <details>

<!-- sdn-diagram:id=connection_response_parse_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=connection_response_parse_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

connection_response_parse_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=connection_response_parse_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Connection Response Parse Guard Specification

## Scenarios

### http client response parse guard

#### guards empty and short status lines before indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_source = rt_file_read_text("src/lib/gc_async_mut/http_client/connection.spl") ?? ""
val nogc_source = rt_file_read_text("src/lib/nogc_async_mut/http_client/connection.spl") ?? ""

expect(gc_source).to_contain("if response_text == \"\":")
expect(gc_source).to_contain("if parts.length() < 3:")
expect(gc_source).to_contain("var status_code = parts[1].parse_int() ?? 0")
expect(nogc_source).to_contain("if response_text == \"\":")
expect(nogc_source).to_contain("if parts.length() < 3:")
expect(nogc_source).to_contain("var status_code = parts[1].parse_int() ?? 0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_client/connection_response_parse_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- http client response parse guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
