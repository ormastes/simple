# Tcp Facade Specification

> <details>

<!-- sdn-diagram:id=tcp_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tcp_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tcp_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tcp_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tcp Facade Specification

## Scenarios

### gc_async_mut TCP facades

#### re-exports TCP tuple helpers and validators

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = tcp_connection_create("127.0.0.1", 8080)
expect(tcp_connection_get_address(conn)).to_equal("127.0.0.1")
expect(tcp_connection_get_port(conn)).to_equal(8080)
expect(tcp_connection_get_state(conn)).to_equal(TCP_STATE_CLOSED)
expect(tcp_state_is_closed(TCP_STATE_CLOSED)).to_equal(true)

val established = tcp_connection_set_state(conn, TCP_STATE_ESTABLISHED)
expect(tcp_state_to_string(TCP_STATE_ESTABLISHED)).to_equal("ESTABLISHED")
expect(tcp_state_can_send(TCP_STATE_ESTABLISHED)).to_equal(true)
expect(tcp_state_can_receive(TCP_STATE_ESTABLISHED)).to_equal(true)
expect(tcp_connection_to_string(established)).to_equal("127.0.0.1:8080 ESTABLISHED")
expect(tcp_connection_equals(established, tcp_connection_clone(established))).to_equal(true)
expect(tcp_connection_is_valid(established)).to_equal(true)
expect(tcp_state_transition_valid(TCP_STATE_CLOSED, TCP_STATE_LISTEN)).to_equal(true)

expect(tcp_ipv4_is_valid("127.0.0.1")).to_equal(true)
expect(tcp_port_is_valid(8080)).to_equal(true)
expect(tcp_address_format("::1", 443)).to_equal("[::1]:443")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/tcp/tcp_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut TCP facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
