# Net Rdma Transport Specification

> Tests covering FR-NET-0006 RDMA exoskeleton transport prototype.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Rdma Transport Specification

## Scenarios

### FR-NET-0006 RDMA exoskeleton transport prototype

#### explicit configuration

#### keeps RDMA disabled by default

- keeps RDMA disabled by default
   - Expected: rdma_is_enabled(config) is false
   - Expected: caps.supports_rdma is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps RDMA disabled by default")
val config = rdma_config_disabled()
val caps = rdma_net_backend_capabilities(config)
expect(rdma_is_enabled(config)).to_equal(false)
expect(caps.supports_rdma).to_equal(false)
```

</details>

#### reports RDMA only for an explicitly enabled protection domain

- reports RDMA only for an explicitly enabled protection domain
   - Expected: rdma_is_enabled(config) is true
   - Expected: caps.supports_rdma is true
   - Expected: net_backend_summary(caps) equals `rdma-test:rdma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports RDMA only for an explicitly enabled protection domain")
val config = rdma_config_explicit("rdma-test", 7u32)
val caps = rdma_net_backend_capabilities(config)
expect(rdma_is_enabled(config)).to_equal(true)
expect(caps.supports_rdma).to_equal(true)
expect(net_backend_summary(caps)).to_equal("rdma-test:rdma")
```

</details>

#### memory and completions

#### tracks memory registration lifetime in Simple-owned types

- tracks memory registration lifetime in Simple-owned types
   - Expected: region.registered is true
   - Expected: region.lkey equals `42u32`
   - Expected: closed.registered is false
   - Expected: closed.lkey equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks memory registration lifetime in Simple-owned types")
val config = rdma_config_explicit("rdma-test", 7u32)
val region = rdma_register_memory(config, 42u64, 0x1000u64, 4096u64, "worker-1")
expect(region.registered).to_equal(true)
expect(region.lkey).to_equal(42u32)
val closed = rdma_deregister_memory(region)
expect(closed.registered).to_equal(false)
expect(closed.lkey).to_equal(0u32)
```

</details>

#### surfaces completion queue polling for worker integration

- surfaces completion queue polling for worker integration
   - Expected: qp.active is true
   - Expected: completion.cq_id equals `18u64`
   - Expected: completion.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surfaces completion queue polling for worker integration")
val config = rdma_config_explicit("rdma-test", 7u32)
val qp = rdma_create_queue_pair(config, 9u64, "worker-1")
val completion = rdma_poll_completion(qp, 100u64, 2048u64, true)
expect(qp.active).to_equal(true)
expect(completion.cq_id).to_equal(18u64)
expect(completion.ok).to_equal(true)
```

</details>

#### benchmark reporting

#### compares portable TCP and RDMA on the same fixture

- compares portable TCP and RDMA on the same fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares portable TCP and RDMA on the same fixture")
val report = rdma_benchmark_report("static-64k", 1000u64, 9000u64, 500u64, 90u64, "rdma-test:rdma")
val line = rdma_benchmark_line(report)
expect(line).to_contain("portable_rps=1000")
expect(line).to_contain("rdma_rps=9000")
expect(line).to_contain("rdma_p95_us=90")
```

</details>

#### hardware provider evidence

#### does not report model or host SFFI providers as hardware RDMA

- does not report model or host SFFI providers as hardware RDMA
   - Expected: rdma_provider_hardware_ready(model) is false
   - Expected: rdma_provider_readiness_reason(model) equals `rdma-not-hardware:model`
   - Expected: rdma_provider_readiness_reason(host) equals `rdma-not-hardware:sffi-host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not report model or host SFFI providers as hardware RDMA")
val model = rdma_provider_evidence("model", "model", false, true, true, true, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")
val host = rdma_provider_evidence("sffi-host", "host-ffi", true, true, true, true, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")
expect(rdma_provider_hardware_ready(model)).to_equal(false)
expect(rdma_provider_readiness_reason(model)).to_equal("rdma-not-hardware:model")
expect(rdma_provider_readiness_reason(host)).to_equal("rdma-not-hardware:sffi-host")
```

</details>

#### requires PCI memory registration queues completion and isolation for rdma device

- requires PCI memory registration queues completion and isolation for rdma device
   - Expected: rdma_provider_readiness_reason(missing_pci) equals `missing-rdma-pci-enumeration`
   - Expected: rdma_provider_readiness_reason(missing_queue) equals `missing-rdma-queue-pair`
   - Expected: rdma_provider_readiness_reason(missing_iommu) equals `missing-rdma-iommu-or-broker`
   - Expected: rdma_provider_hardware_ready(ready) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PCI memory registration queues completion and isolation for rdma device")
val missing_pci = rdma_provider_evidence("device", "simple-driver", false, true, true, true, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")
val missing_queue = rdma_provider_evidence("device", "simple-driver", true, true, true, false, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")
val missing_iommu = rdma_provider_evidence("device", "simple-driver", true, true, true, true, true, true, false, "raw-device-grant:tok=1", "non-secure-resource-namespace")
val ready = rdma_provider_evidence("device", "simple-driver", true, true, true, true, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")

expect(rdma_provider_readiness_reason(missing_pci)).to_equal("missing-rdma-pci-enumeration")
expect(rdma_provider_readiness_reason(missing_queue)).to_equal("missing-rdma-queue-pair")
expect(rdma_provider_readiness_reason(missing_iommu)).to_equal("missing-rdma-iommu-or-broker")
expect(rdma_provider_hardware_ready(ready)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_rdma_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0006 RDMA exoskeleton transport prototype.
- FR-NET-0006 RDMA exoskeleton transport prototype

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `8f7463a2b3c02c5682450a581b4a6773c3919c267d7e2a1d3e350e2fcadc28c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f7463a2b3c02c5682450a581b4a6773c3919c267d7e2a1d3e350e2fcadc28c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f7463a2b3c02c5682450a581b4a6773c3919c267d7e2a1d3e350e2fcadc28c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/net_rdma_transport_spec.spl
mirror: doc/06_spec/03_system/os/net_rdma_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_rdma_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_rdma_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_rdma_transport_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RDMA disabled by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_rdma_transport_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports RDMA only for an explicitly enabled protection domain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_rdma_transport_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks memory registration lifetime in Simple-owned types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
