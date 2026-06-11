# Stomp Facade Specification

> <details>

<!-- sdn-diagram:id=stomp_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stomp_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stomp_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stomp_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stomp Facade Specification

## Scenarios

### nogc_async_mut STOMP facades

#### re-exports constants and heartbeat helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(stomp_cmd_connect()).to_equal("CONNECT")
expect(stomp_cmd_send()).to_equal("SEND")
expect(stomp_header_destination()).to_equal("destination")
expect(stomp_ack_client()).to_equal("client")
expect(stomp_null_byte()).to_equal("\0")

val heartbeat = parse_heartbeat("1000,2000")
expect(heartbeat[0]).to_equal(1000)
expect(heartbeat[1]).to_equal(2000)
expect(format_heartbeat(1000, 2000)).to_equal("1000,2000")

val negotiated = negotiate_heartbeat(parse_heartbeat("1000,1000"), parse_heartbeat("500,2000"))
expect(negotiated[0]).to_equal(2000)
expect(negotiated[1]).to_equal(1000)
expect(is_heartbeat_disabled(parse_heartbeat("0,0"))).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/stomp/stomp_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut STOMP facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
