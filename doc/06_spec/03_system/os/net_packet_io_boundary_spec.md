# Net Packet Io Boundary Specification

> Tests covering FR-NET-0004 packet I/O backend boundary.

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

- keeps portable sockets as the default backend
   - Expected: caps.backend_name equals `portable-socket`
   - Expected: caps.supports_packet_io is false
   - Expected: packet_io_disabled_capabilities().supports_packet_io is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps portable sockets as the default backend")
val caps = portable_net_backend_capabilities()
expect(caps.backend_name).to_equal("portable-socket")
expect(caps.supports_packet_io).to_equal(false)
expect(packet_io_disabled_capabilities().supports_packet_io).to_equal(false)
```

</details>

#### reports packet I/O only for explicit packet-ring backends

- reports packet I/O only for explicit packet-ring backends
   - Expected: portable_accel.supports_packet_io is false
   - Expected: packet.supports_packet_io is true
   - Expected: net_backend_summary(packet) equals `xdp-test:zero-copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports packet I/O only for explicit packet-ring backends")
val portable_accel = accelerated_net_backend_capabilities("uring", false, false, false)
val packet = packet_io_net_backend_capabilities("xdp-test", false, false)
expect(portable_accel.supports_packet_io).to_equal(false)
expect(packet.supports_packet_io).to_equal(true)
expect(net_backend_summary(packet)).to_equal("xdp-test:zero-copy")
```

</details>

#### ring ownership

#### leases RX and TX buffers to the application and returns them to the driver

- leases RX and TX buffers to the application and returns them to the driver
   - Expected: caps.supports_packet_io is true
   - Expected: caps.rx_entries equals `512u32`
   - Expected: caps.tx_entries equals `512u32`
   - Expected: rx.owner equals `application`
   - Expected: tx.owner equals `application`
   - Expected: done.owner equals `driver`
   - Expected: done.completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leases RX and TX buffers to the application and returns them to the driver")
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

- compares portable async sockets and packet I/O on the same fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares portable async sockets and packet I/O on the same fixture")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0004 packet I/O backend boundary.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7e23c4813394c3c71d85c8fd966477ead09d2881068c42b75a107565e477604`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7e23c4813394c3c71d85c8fd966477ead09d2881068c42b75a107565e477604`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7e23c4813394c3c71d85c8fd966477ead09d2881068c42b75a107565e477604`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/net_packet_io_boundary_spec.spl
mirror: doc/06_spec/03_system/os/net_packet_io_boundary_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_packet_io_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_packet_io_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_packet_io_boundary_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps portable sockets as the default backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_packet_io_boundary_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports packet I/O only for explicit packet-ring backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_packet_io_boundary_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leases RX and TX buffers to the application and returns them to the driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
