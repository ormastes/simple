# Riscv Target Specification

> <details>

<!-- sdn-diagram:id=riscv_target_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_target_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_target_spec -> compiler
riscv_target_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_target_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Target Specification

## Scenarios

### RISC-V backend target contracts

#### defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("lp64d")
expect(contract.march).to_equal("rv64gc")
expect(contract.abi_flag()).to_equal("-mabi=lp64d")
expect(contract.march_flag()).to_equal("-march=rv64gc")
```

</details>

#### defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.triple()).to_equal("riscv32-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("ilp32d")
expect(contract.march).to_equal("rv32gc")
expect(contract.pointer_bits).to_equal(32)
```

</details>

#### keeps compiler and hardware aligned on the RV32 Linux contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler_contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
val platform = qemu_virt_rv32_platform_profile()
expect(compiler_contract.pointer_bits).to_equal(platform.linux.xlen)
expect(compiler_contract.abi).to_equal(platform.linux.abi)
expect(platform.name).to_equal("qemu_virt_rv32")
expect(platform.linux.mmu_mode.to_text()).to_equal("sv32")
```

</details>

#### keeps compiler and hardware aligned on the RV64-first Linux contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler_contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
val platform = qemu_virt_rv64_platform_profile()
expect(compiler_contract.pointer_bits).to_equal(platform.linux.xlen)
expect(compiler_contract.abi).to_equal(platform.linux.abi)
expect(platform.name).to_equal("qemu_virt_rv64")
expect(platform.linux.mmu_mode.to_text()).to_equal("sv39")
```

</details>

#### keeps bare-metal contracts on none-elf triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_baremetal_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-none-elf")
expect(contract.sysroot).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/riscv_target_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V backend target contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
