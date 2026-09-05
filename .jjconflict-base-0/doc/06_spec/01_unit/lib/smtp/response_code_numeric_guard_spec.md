# Response Code Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=response_code_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=response_code_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

response_code_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=response_code_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Response Code Numeric Guard Specification

## Scenarios

### smtp response code numeric guard

#### defaults malformed response code parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nogc_sync = rt_file_read_text("src/lib/nogc_sync_mut/smtp/types.spl") ?? ""
val nogc_async = rt_file_read_text("src/lib/nogc_async_mut/smtp/types.spl") ?? ""
val gc_async = rt_file_read_text("src/lib/gc_async_mut/smtp/types.spl") ?? ""

expect(nogc_sync).to_contain("return code_str.to_int() ?? 0")
expect(nogc_async).to_contain("return code_str.to_int() ?? 0")
expect(gc_async).to_contain("return code_str.to_int() ?? 0")
expect(nogc_sync.contains("return code_str.to_int()\n")).to_equal(false)
expect(nogc_async.contains("return code_str.to_int()\n")).to_equal(false)
expect(gc_async.contains("return code_str.to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/smtp/response_code_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- smtp response code numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
