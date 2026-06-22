# Dma Safety Gate Specification

> <details>

<!-- sdn-diagram:id=dma_safety_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dma_safety_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dma_safety_gate_spec -> std
dma_safety_gate_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dma_safety_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dma Safety Gate Specification

## Scenarios

### dma safety gate hardening acceptance

#### accepts the direct DMA path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = DisplayDmaFallbackGate.with_dma()
expect(gate.effective_path()).to_equal("dma")
expect(gate.hardening_acceptance_ready()).to_equal(true)
expect(gate.hardening_acceptance_reason()).to_equal("ready")
```

</details>

#### keeps framebuffer fallback diagnostic-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = DisplayDmaFallbackGate.fallback_only()
expect(gate.effective_path()).to_equal("framebuffer")
expect(gate.hardening_acceptance_ready()).to_equal(false)
expect(gate.hardening_acceptance_reason()).to_equal("display-dma-fallback-diagnostic:framebuffer")
```

</details>

#### accepts SR-IOV hardening only with IOMMU isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = SriovIsolationGate.request_vf(true)
expect(gate.can_proceed()).to_equal(true)
expect(gate.hardening_acceptance_ready()).to_equal(true)
expect(gate.hardening_acceptance_reason()).to_equal("ready")
```

</details>

#### keeps trusted no-IOMMU SR-IOV diagnostic-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = SriovIsolationGate.trusted_no_iommu()
expect(gate.can_proceed()).to_equal(false)
expect(gate.hardening_acceptance_ready()).to_equal(false)
expect(gate.hardening_acceptance_reason()).to_equal("sriov-trust-mode-diagnostic:trusted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/dma/dma_safety_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dma safety gate hardening acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
