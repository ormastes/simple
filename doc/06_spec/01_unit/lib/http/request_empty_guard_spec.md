# Request Empty Guard Specification

> <details>

<!-- sdn-diagram:id=request_empty_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=request_empty_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

request_empty_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=request_empty_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Request Empty Guard Specification

## Scenarios

### nogc http request empty input guard

#### returns a default request before indexing split lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/http/request.spl") ?? ""
val sync_source = rt_file_read_text("src/lib/nogc_sync_mut/http/request.spl") ?? ""

expect(source).to_contain("if text == \"\":")
expect(source).to_contain("return (\"GET\", \"/\", \"HTTP/1.1\", [], \"\")")
expect(source).to_contain("val request_line = if lines.length() > 0: lines[0] else: \"\"")
expect(sync_source).to_contain("if text == \"\":")
expect(sync_source).to_contain("return (\"GET\", \"/\", \"HTTP/1.1\", [], \"\")")
expect(sync_source).to_contain("val request_line = if lines.length() > 0: lines[0] else: \"\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http/request_empty_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc http request empty input guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
