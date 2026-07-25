# Net Packet Io Boundary Specification

> <details>

<!-- sdn-diagram:id=net_packet_io_boundary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_packet_io_boundary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_packet_io_boundary_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_packet_io_boundary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Packet Io Boundary Specification

## Scenarios

### FR-NET-0004 packet I/O backend boundary

#### capability gating

#### keeps portable sockets as the default backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
expect(caps.backend_name).to_equal("portable-socket")
expect(caps.supports_packet_io).to_equal(false)
expect(packet_io_disabled_capabilities().supports_packet_io).to_equal(false)
```

</details>

#### reports packet I/O only for explicit packet-ring backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val portable_accel = accelerated_net_backend_capabilities("uring", false, false, false)
val packet = packet_io_net_backend_capabilities("xdp-test", false, false)
expect(portable_accel.supports_packet_io).to_equal(false)
expect(packet.supports_packet_io).to_equal(true)
expect(net_backend_summary(packet)).to_equal("xdp-test:zero-copy")
```

</details>

#### ring ownership

#### leases RX and TX buffers to the application and returns them to the driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = packet_io_opt_in_capabilities(512u32, 512u32, true)
expect(caps.supports_packet_io).to_equal(true)
expect(caps.rx_entries).to_equal(512u32)
expect(caps.tx_entries).to_equal(512u32)

val rx = packet_rx_lease(10u64, 1u64, 1500u64)
val tx = packet_tx_lease(10u64, 2u64, 512u64)
expect(rx.owner).to_equal("application")
expect(tx.owner).to_equal("application")

val done = packet_complete(tx)
expect(done.owner).to_equal("driver")
expect(done.completed).to_equal(true)
```

</details>

#### benchmark reporting

#### compares portable async sockets and packet I/O on the same fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = packet_io_benchmark_report("http-static-64k", 1000u64, 4000u64, 120u64, 40u64, "xdp-test:zero-copy")
val line = packet_io_benchmark_line(report)
expect(line).to_contain("http-static-64k")
expect(line).to_contain("portable_pps=1000")
expect(line).to_contain("packet_io_pps=4000")
expect(line).to_contain("packet_io_p50_us=40")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_packet_io_boundary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0004 packet I/O backend boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
