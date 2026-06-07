# Net Backend Specification

> <details>

<!-- sdn-diagram:id=net_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Backend Specification

## Scenarios

### async net backend capabilities

#### uses portable defaults for QEMU and hosted CI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
expect(caps.backend_name).to_equal("portable-socket")
expect(caps.supports_async).to_equal(false)
expect(net_backend_acceleration_tier(caps)).to_equal("portable")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(false)
```

</details>

#### reports RDMA as the strongest explicit acceleration tier

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = accelerated_net_backend_capabilities("rdma-test", true, true, true)
expect(caps.supports_packet_io).to_equal(true)
expect(caps.supports_sriov).to_equal(true)
expect(caps.supports_rdma).to_equal(true)
expect(net_backend_acceleration_tier(caps)).to_equal("rdma")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(true)
expect(net_backend_summary(caps)).to_equal("rdma-test:rdma")
```

</details>

#### keeps packet I/O disabled unless explicitly configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val portable = portable_net_backend_capabilities()
val accelerated = accelerated_net_backend_capabilities("uring", false, false, false)
val packet = packet_io_net_backend_capabilities("xdp-test", false, false)

expect(portable.supports_packet_io).to_equal(false)
expect(accelerated.supports_packet_io).to_equal(false)
expect(packet.supports_packet_io).to_equal(true)
expect(net_backend_acceleration_tier(packet)).to_equal("zero-copy")
```

</details>

#### models packet ring ownership and completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disabled = packet_io_disabled_capabilities()
expect(disabled.supports_packet_io).to_equal(false)

val enabled = packet_io_opt_in_capabilities(1024u32, 1024u32, true)
expect(enabled.supports_packet_io).to_equal(true)
expect(enabled.zero_copy).to_equal(true)

val rx = packet_rx_lease(1u64, 7u64, 1500u64)
expect(rx.direction).to_equal("rx")
expect(rx.owner).to_equal("application")
expect(rx.completed).to_equal(false)

val tx = packet_tx_lease(1u64, 8u64, 64u64)
val done = packet_complete(tx)
expect(done.direction).to_equal("tx")
expect(done.owner).to_equal("driver")
expect(done.completed).to_equal(true)
```

</details>

#### renders comparable packet I/O benchmark output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = packet_io_benchmark_report("http-static-64k", 1000u64, 4000u64, 120u64, 40u64, "xdp-test:zero-copy")
val line = packet_io_benchmark_line(report)
expect(line).to_contain("portable_pps=1000")
expect(line).to_contain("packet_io_pps=4000")
expect(line).to_contain("backend=xdp-test:zero-copy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/io/net_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- async net backend capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
