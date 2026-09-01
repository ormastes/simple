# Net Backend Specification

> Tests covering async net backend capabilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Backend Specification

## Scenarios

### async net backend capabilities

#### uses portable defaults for QEMU and hosted CI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses portable defaults for QEMU and hosted CI
   - Expected: caps.backend_name equals `portable-socket`
   - Expected: caps.supports_async is false
   - Expected: net_backend_acceleration_tier(caps) equals `portable`
   - Expected: net_backend_can_accelerate_static_files(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses portable defaults for QEMU and hosted CI")
val caps = portable_net_backend_capabilities()
expect(caps.backend_name).to_equal("portable-socket")
expect(caps.supports_async).to_equal(false)
expect(net_backend_acceleration_tier(caps)).to_equal("portable")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(false)
```

</details>

#### reports RDMA as the strongest explicit acceleration tier

- reports RDMA as the strongest explicit acceleration tier
   - Expected: caps.supports_packet_io is true
   - Expected: caps.supports_sriov is true
   - Expected: caps.supports_rdma is true
   - Expected: net_backend_acceleration_tier(caps) equals `rdma`
   - Expected: net_backend_can_accelerate_static_files(caps) is true
   - Expected: net_backend_summary(caps) equals `rdma-test:rdma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports RDMA as the strongest explicit acceleration tier")
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

- keeps packet I/O disabled unless explicitly configured
   - Expected: portable.supports_packet_io is false
   - Expected: accelerated.supports_packet_io is false
   - Expected: packet.supports_packet_io is true
   - Expected: net_backend_acceleration_tier(packet) equals `zero-copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps packet I/O disabled unless explicitly configured")
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

- models packet ring ownership and completion
   - Expected: disabled.supports_packet_io is false
   - Expected: enabled.supports_packet_io is true
   - Expected: enabled.zero_copy is true
   - Expected: rx.direction equals `rx`
   - Expected: rx.owner equals `application`
   - Expected: rx.completed is false
   - Expected: done.direction equals `tx`
   - Expected: done.owner equals `driver`
   - Expected: done.completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models packet ring ownership and completion")
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

- renders comparable packet I/O benchmark output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders comparable packet I/O benchmark output")
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
| Source | `test/unit/lib/nogc_async_mut/io/net_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering async net backend capabilities.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c505339aded5685daeec19b50f57c1d3e79a2c30baa28725c8faa6894de4ce6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c505339aded5685daeec19b50f57c1d3e79a2c30baa28725c8faa6894de4ce6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c505339aded5685daeec19b50f57c1d3e79a2c30baa28725c8faa6894de4ce6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/io/net_backend_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/io/net_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/io/net_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/io/net_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/io/net_backend_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses portable defaults for QEMU and hosted CI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/io/net_backend_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports RDMA as the strongest explicit acceleration tier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/io/net_backend_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps packet I/O disabled unless explicitly configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
