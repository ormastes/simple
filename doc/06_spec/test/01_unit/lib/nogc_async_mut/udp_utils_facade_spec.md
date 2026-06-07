# Udp Utils Facade Specification

> <details>

<!-- sdn-diagram:id=udp_utils_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=udp_utils_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

udp_utils_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=udp_utils_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Udp Utils Facade Specification

## Scenarios

### nogc_async_mut udp_utils facade

#### re-exports UDP socket and datagram helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val socket = bind_socket(create_udp_socket(), "127.0.0.1", 9000)
expect(is_socket_bound(socket)).to_equal(1)
expect(get_socket_endpoint(socket)).to_equal("127.0.0.1:9000")
expect(is_socket_closed(close_socket(socket))).to_equal(1)

val tuned = set_multicast_ttl(enable_broadcast(create_udp_socket_with_buffer_sizes(512, 512)), 4)
expect(is_broadcast_enabled(tuned)).to_equal(1)
expect(get_multicast_ttl(tuned)).to_equal(4)
val joined = join_multicast_group(socket, "224.0.0.1")
expect(is_in_multicast_group(joined, "224.0.0.1")).to_equal(1)

val datagram = create_datagram("127.0.0.1", 9000, "224.0.0.1", 9001, "hello")
expect(validate_datagram(datagram)).to_equal(1)
expect(get_datagram_size(datagram)).to_equal(13)
expect(get_datagram_source(datagram)).to_equal("127.0.0.1:9000")
expect(get_datagram_destination(datagram)).to_equal("224.0.0.1:9001")
expect(compare_datagrams(datagram, create_reply_datagram(create_reply_datagram(datagram, "hello"), "hello"))).to_equal(1)

expect(is_valid_port(65535)).to_equal(1)
expect(is_well_known_port(80)).to_equal(1)
expect(is_registered_port(8080)).to_equal(1)
expect(is_dynamic_port(60000)).to_equal(1)
expect(is_ipv4_address("127.0.0.1")).to_equal(1)
expect(is_ipv6_address("::1")).to_equal(1)
expect(is_multicast_ipv4("224.0.0.1")).to_equal(1)
expect(is_broadcast_address("255.255.255.255")).to_equal(1)
expect(is_loopback_address("127.0.0.1")).to_equal(1)
expect(is_any_address("0.0.0.0")).to_equal(1)

expect(needs_fragmentation("small")).to_equal(0)
expect(calculate_fragment_count("abcdef", 2)).to_equal(3)
expect(create_fragment("abcdef", 2, 3)).to_equal("cde")
expect(get_max_payload_size()).to_equal(65499)
expect(can_send_datagram(socket, datagram)).to_equal(1)
expect(can_send_broadcast(enable_broadcast(socket), create_datagram("127.0.0.1", 9000, "255.255.255.255", 9001, "hello"))).to_equal(1)
expect(can_send_multicast(socket, datagram)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/udp_utils_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut udp_utils facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
