# Rv64 Linux Platform Contract Specification

> <details>

<!-- sdn-diagram:id=rv64_linux_platform_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_linux_platform_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_linux_platform_contract_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_linux_platform_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Linux Platform Contract Specification

## Scenarios

### RV64 Linux platform contract

#### uses the QEMU virt memory map and Linux entry registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = RiscvPlatformProfile.qemu_virt_rv64()
expect(platform.dram_base).to_equal(0x80000000)
expect(platform.uart_base).to_equal(0x10000000)
expect(platform.clint_base).to_equal(0x02000000)
expect(platform.plic_base).to_equal(0x0C000000)
expect(platform.hartid_register).to_equal("a0")
expect(platform.dtb_register).to_equal("a1")
```

</details>

#### uses LP64D Sv39 for the first Linux milestone

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linux = RiscvLinuxProfile.rv64_qemu_virt_linux()
expect(linux.abi.to_text()).to_equal("lp64d")
expect(linux.mmu_mode.to_text()).to_equal("sv39")
expect(linux.kernel_alignment).to_equal(0x200000)
expect(linux.opensbi_required).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/hardware/rv64gc/rv64_linux_platform_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV64 Linux platform contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
