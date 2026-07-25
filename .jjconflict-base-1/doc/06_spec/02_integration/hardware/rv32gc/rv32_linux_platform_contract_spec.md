# Rv32 Linux Platform Contract Specification

> <details>

<!-- sdn-diagram:id=rv32_linux_platform_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_linux_platform_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_linux_platform_contract_spec -> std
rv32_linux_platform_contract_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_linux_platform_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32 Linux Platform Contract Specification

## Scenarios

### RV32 Linux platform contract

#### uses the QEMU virt memory map and Linux entry registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = RiscvPlatformProfile.qemu_virt_rv32()
expect(platform.dram_base).to_equal(0x80000000)
expect(platform.uart_base).to_equal(0x10000000)
expect(platform.clint_base).to_equal(0x02000000)
expect(platform.plic_base).to_equal(0x0C000000)
expect(platform.hartid_register).to_equal("a0")
expect(platform.dtb_register).to_equal("a1")
```

</details>

#### uses ILP32D Sv32 for the first Linux milestone

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linux = RiscvLinuxProfile.rv32_qemu_virt_linux()
expect(linux.abi.to_text()).to_equal("ilp32d")
expect(linux.mmu_mode.to_text()).to_equal("sv32")
expect(linux.kernel_alignment).to_equal(0x200000)
expect(linux.opensbi_required).to_equal(true)
```

</details>

#### programs the Linux handoff registers with satp disabled

1. var soc = rv32 soc create
2. soc set linux handoff
   - Expected: soc.regs.read(10) equals `0`
   - Expected: soc.regs.read(11) equals `0x88000000`
   - Expected: soc.csr.read_satp() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = RiscvPlatformProfile.qemu_virt_rv32()
var soc = rv32_soc_create(1, 0x1000, platform.reset_vector)
soc.set_linux_handoff(0, 0x88000000)
expect(soc.regs.read(10)).to_equal(0)
expect(soc.regs.read(11)).to_equal(0x88000000)
expect(soc.csr.read_satp()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32 Linux platform contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
