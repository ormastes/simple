# Mcp Sdk Transport Facade Specification

> 1. set json lines mode

<!-- sdn-diagram:id=mcp_sdk_transport_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_sdk_transport_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_sdk_transport_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_sdk_transport_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Sdk Transport Facade Specification

## Scenarios

### nogc_async_mut mcp sdk transport facade

#### re-exports stdio framing state and content-length helpers

1. set json lines mode
   - Expected: is_json_lines_mode() is true
   - Expected: is_framing_detected() is true
2. set json lines mode
   - Expected: is_json_lines_mode() is false
   - Expected: content_length_header("{}") equals `Content-Length: 2\r\n\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_json_lines_mode(true)
expect(is_json_lines_mode()).to_equal(true)
expect(is_framing_detected()).to_equal(true)
set_json_lines_mode(false)
expect(is_json_lines_mode()).to_equal(false)
expect(content_length_header("{}")).to_equal("Content-Length: 2\r\n\r\n")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/mcp_sdk/transport/mcp_sdk_transport_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut mcp sdk transport facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
