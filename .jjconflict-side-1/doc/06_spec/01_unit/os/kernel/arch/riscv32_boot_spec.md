# Riscv32 Boot Specification

> 1. boot save boot params

<!-- sdn-diagram:id=riscv32_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv32_boot_spec -> std
riscv32_boot_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Boot Specification

## Scenarios

### rv32 boot bootstrap trap runtime

#### records boot arguments

1. boot save boot params
   - Expected: boot.hart_id() equals `7`
   - Expected: boot.dtb_addr() equals `0x88001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot = Rv32Boot(direct_boot: true)
boot.save_boot_params(7, 0x88001000)
expect(boot.hart_id()).to_equal(7)
expect(boot.dtb_addr()).to_equal(0x88001000)
```

</details>

#### keeps the fixed kernel load address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot = Rv32Boot(direct_boot: true)
expect(boot.kernel_load_addr()).to_equal(0x80000000)
```

</details>

#### builds an RV32 boot output with direct-boot defaults

1. boot save boot params
   - Expected: boot_output.arch equals `Architecture.Riscv32`
   - Expected: boot_output.serial_base equals `0x10000000`
   - Expected: boot_output.kernel_phys_base.addr equals `0x80000000`
   - Expected: boot_output.memory_map.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boot = Rv32Boot(direct_boot: true)
boot.save_boot_params(0, 0)
val boot_output = boot.build_boot_output()
expect(boot_output.arch).to_equal(Architecture.Riscv32)
expect(boot_output.serial_base).to_equal(0x10000000)
expect(boot_output.kernel_phys_base.addr).to_equal(0x80000000)
expect(boot_output.memory_map.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv32_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rv32 boot bootstrap trap runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
