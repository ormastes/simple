# Nvme Freestanding Controller Specification

> <details>

<!-- sdn-diagram:id=nvme_freestanding_controller_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_freestanding_controller_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_freestanding_controller_spec -> std
nvme_freestanding_controller_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_freestanding_controller_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Freestanding Controller Specification

## Scenarios

### freestanding NVMe controller resources

#### builds system-driver controller evidence without hosted syscalls

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resources = _system_resources()
val controller = nvme_freestanding_controller_from_resources(resources).unwrap()
val missing_probe = nvme_freestanding_transfer_evidence(controller, false, false, false, false)

expect(missing_probe.driver_placement).to_equal("system-driver")
expect(missing_probe.grant_kind).to_equal("kernel-owned-resource")
expect(missing_probe.namespace_mode).to_equal("system-kernel-namespace")
expect(nvme_transfer_readiness_reason(missing_probe)).to_equal("missing-nvme-completion")
```

</details>

#### only reports ready after actual completion and reversible sector probes are supplied

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = nvme_freestanding_controller_from_resources(_system_resources()).unwrap()
val probe = nvme_sector_probe_result(0u64, 512u64, 0u32, true, true, true, true)
val ready = nvme_freestanding_transfer_evidence_from_probe(controller, probe)

expect(nvme_sector_probe_reason(probe)).to_equal("ready")
expect(nvme_transfer_readiness_reason(ready)).to_equal("ready")
```

</details>

#### rejects probe evidence that bypasses shared transfer logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = nvme_freestanding_controller_from_resources(_system_resources()).unwrap()
val probe = nvme_sector_probe_result(0u64, 512u64, 0u32, true, true, true, false)
val evidence = nvme_freestanding_transfer_evidence_from_probe(controller, probe)

expect(nvme_sector_probe_reason(probe)).to_equal("nvme-sector-probe-not-shared-transfer")
expect(nvme_transfer_readiness_reason(evidence)).to_contain("missing-common-driver-logic")
```

</details>

#### rejects invalid controller resources before transfer evidence can be built

1. var resources =  system resources
2. resources admin =  queue
   - Expected: nvme_freestanding_controller_resource_reason(resources) equals `nvme-freestanding-admin-qid-not-zero`
3. resources =  system resources
4. resources io =  queue
   - Expected: nvme_freestanding_controller_resource_reason(resources) equals `nvme-freestanding-io-qid-zero`
5. resources =  system resources
   - Expected: nvme_freestanding_controller_from_resources(resources).unwrap_err() equals `nvme-freestanding-dma-not-isolated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = _system_resources()
resources.admin = _queue(1u16, 0x200000u64)
expect(nvme_freestanding_controller_resource_reason(resources)).to_equal("nvme-freestanding-admin-qid-not-zero")

resources = _system_resources()
resources.io = _queue(0u16, 0x220000u64)
expect(nvme_freestanding_controller_resource_reason(resources)).to_equal("nvme-freestanding-io-qid-zero")

resources = _system_resources()
resources.dma_isolated = false
expect(nvme_freestanding_controller_from_resources(resources).unwrap_err()).to_equal("nvme-freestanding-dma-not-isolated")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- freestanding NVMe controller resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
