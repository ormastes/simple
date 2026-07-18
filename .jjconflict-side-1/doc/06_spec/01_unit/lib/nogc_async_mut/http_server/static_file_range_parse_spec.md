# Static File Range Parse Specification

> <details>

<!-- sdn-diagram:id=static_file_range_parse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_file_range_parse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_file_range_parse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_file_range_parse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static File Range Parse Specification

## Scenarios

### static file Range parsing

#### parses bounded byte range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = static_file_parse_range("bytes=2-4", 10)
expect(range[0]).to_equal(2)
expect(range[1]).to_equal(4)
```

</details>

#### rejects overflowing range numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = static_file_parse_range("bytes=999999999999999999999999999999-", 10)
expect(range[0]).to_equal(-1)
expect(range[1]).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- static file Range parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
