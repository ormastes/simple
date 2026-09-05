# Net Rdma Transport Specification

> <details>

<!-- sdn-diagram:id=net_rdma_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_rdma_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_rdma_transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_rdma_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = rdma_config_disabled()
val caps = rdma_net_backend_capabilities(config)
expect(rdma_is_enabled(config)).to_equal(false)
expect(caps.supports_rdma).to_equal(false)
```

</details>

#### reports RDMA only for an explicitly enabled protection domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = rdma_config_explicit("rdma-test", 7u32)
val caps = rdma_net_backend_capabilities(config)
expect(rdma_is_enabled(config)).to_equal(true)
expect(caps.supports_rdma).to_equal(true)
expect(net_backend_summary(caps)).to_equal("rdma-test:rdma")
```

</details>

#### memory and completions

#### tracks memory registration lifetime in Simple-owned types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rdma_benchmark_report("static-64k", 1000u64, 9000u64, 500u64, 90u64, "rdma-test:rdma")
val line = rdma_benchmark_line(report)
expect(line).to_contain("portable_rps=1000")
expect(line).to_contain("rdma_rps=9000")
expect(line).to_contain("rdma_p95_us=90")
```

</details>

#### hardware provider evidence

#### does not report model or host SFFI providers as hardware RDMA

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = rdma_provider_evidence("model", "model", false, true, true, true, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")
val host = rdma_provider_evidence("sffi-host", "host-ffi", true, true, true, true, true, true, true, "raw-device-grant:tok=1", "non-secure-resource-namespace")
expect(rdma_provider_hardware_ready(model)).to_equal(false)
expect(rdma_provider_readiness_reason(model)).to_equal("rdma-not-hardware:model")
expect(rdma_provider_readiness_reason(host)).to_equal("rdma-not-hardware:sffi-host")
```

</details>

#### requires PCI memory registration queues completion and isolation for rdma device

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
