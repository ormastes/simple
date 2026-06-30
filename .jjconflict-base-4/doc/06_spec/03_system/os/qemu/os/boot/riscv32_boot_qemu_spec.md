# Riscv32 Boot Qemu Specification

> <details>

<!-- sdn-diagram:id=riscv32_boot_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_boot_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv32_boot_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_boot_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Boot Qemu Specification

## Scenarios

### RISC-V 32 Architecture Boot

<details>
<summary>Advanced: binds the canonical RV32 boot artifact contract</summary>

#### binds the canonical RV32 boot artifact contract _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(ARCH)
expect(target.arch).to_equal(Architecture.Riscv32)
expect(target.entry).to_equal("src/os/kernel/arch/riscv32/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/riscv32/linker.ld")
expect(target.target_triple).to_equal("riscv32-unknown-none")
expect(target.output).to_equal("build/os/simpleos_riscv32.elf")
expect(target.qemu_system).to_equal("qemu-system-riscv32")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("rv32")
expect(target.qemu_memory).to_equal("128M")
expect(target.qemu_bios).to_equal("none")
expect(target.qemu_extra.len()).to_equal(0)
expect(rt_file_exists(target.output)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: UART initialized in direct boot</summary>

#### UART initialized in direct boot _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("UART")
```

</details>


</details>

<details>
<summary>Advanced: prints RISC-V 32 architecture identifier</summary>

#### prints RISC-V 32 architecture identifier _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("RISC-V 32")
```

</details>


</details>

<details>
<summary>Advanced: memory map parsed</summary>

#### memory map parsed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: RAM at 0x80000000</summary>

#### RAM at 0x80000000 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("0x80000000")
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes</summary>

#### boot sequence completes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: initializes noalloc boot memory services</summary>

#### initializes noalloc boot memory services _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("LOG OK")
    expect(output).to_contain("MEM OK")
    expect(output).to_contain("PMM OK")
    expect(output).to_contain("HEAP OK")
    expect(output).to_contain("SVC OK")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V 32 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
