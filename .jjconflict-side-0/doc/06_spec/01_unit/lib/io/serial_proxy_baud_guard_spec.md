# Serial Proxy Baud Guard Specification

> <details>

<!-- sdn-diagram:id=serial_proxy_baud_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serial_proxy_baud_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serial_proxy_baud_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serial_proxy_baud_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Proxy Baud Guard Specification

## Scenarios

### serial proxy baud guard

#### guards malformed baud values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/io/serial_proxy.spl") ?? ""

expect(source).to_contain("fn parse_baud_or_zero(value: text) -> i64")
expect(source).to_contain("return trimmed.to_int() ?? 0")
expect(source).to_contain("val baud = parse_baud_or_zero(args[1])")
expect(source).to_contain("if baud <= 0:")
expect(source.contains("val baud = args[1].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/serial_proxy_baud_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- serial proxy baud guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
