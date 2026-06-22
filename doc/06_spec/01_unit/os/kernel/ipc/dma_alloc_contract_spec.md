# Dma Alloc Contract Specification

> <details>

<!-- sdn-diagram:id=dma_alloc_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dma_alloc_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dma_alloc_contract_spec -> std
dma_alloc_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dma_alloc_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dma Alloc Contract Specification

## Scenarios

### DMA allocation syscall contract

#### uses syscall return as virtual address and result words as phys plus allocation id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = dma_alloc_syscall_view(0x80000000, 0x40000000u64, 77u64)
expect(view.is_ok()).to_equal(true)
val dma = view.unwrap()
expect(dma.virt_addr).to_equal(0x80000000u64)
expect(dma.phys_addr).to_equal(0x40000000u64)
expect(dma.allocation_id).to_equal(77u64)
```

</details>

#### rejects missing physical address or allocation id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dma_alloc_syscall_view(0x80000000, 0u64, 77u64).unwrap_err()).to_equal("dma-alloc-missing-phys")
expect(dma_alloc_syscall_view(0x80000000, 0x40000000u64, 0u64).unwrap_err()).to_equal("dma-alloc-missing-allocation-id")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/dma_alloc_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DMA allocation syscall contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
