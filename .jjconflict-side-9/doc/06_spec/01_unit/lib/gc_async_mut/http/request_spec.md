# Request Specification

> <details>

<!-- sdn-diagram:id=request_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=request_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

request_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=request_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Request Specification

## Scenarios

### gc_async_mut HTTP request parsing

#### falls back for malformed request line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_request_line("GET")
expect(parsed[0]).to_equal("GET")
expect(parsed[1]).to_equal("/")
expect(parsed[2]).to_equal("HTTP/1.1")
```

</details>

#### falls back for empty request text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_request("")
expect(parsed[0]).to_equal("GET")
expect(parsed[1]).to_equal("/")
expect(parsed[2]).to_equal("HTTP/1.1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/http/request_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut HTTP request parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
