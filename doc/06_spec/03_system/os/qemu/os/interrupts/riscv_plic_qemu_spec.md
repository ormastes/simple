# Riscv Plic Qemu Specification

> <details>

<!-- sdn-diagram:id=riscv_plic_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_plic_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_plic_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_plic_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Plic Qemu Specification

## Scenarios

### RISC-V 32 PLIC

<details>
<summary>Advanced: interrupt controller initialized</summary>

#### interrupt controller initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: interrupt init pass reported</summary>

#### interrupt init pass reported _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

### RISC-V 64 PLIC

<details>
<summary>Advanced: interrupt controller initialized</summary>

#### interrupt controller initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: interrupt init pass reported</summary>

#### interrupt init pass reported _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/interrupts/riscv_plic_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V 32 PLIC
- RISC-V 64 PLIC

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
