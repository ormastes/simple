# Software Int Qemu Specification

> <details>

<!-- sdn-diagram:id=software_int_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=software_int_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

software_int_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=software_int_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Software Int Qemu Specification

## Scenarios

### Software Interrupts ARM64 (SVC)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

### Software Interrupts x86_64 (INT/SYSCALL)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

### Software Interrupts RISC-V 32 (ECALL)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

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
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

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

### Software Interrupts RISC-V 64 (ECALL)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

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
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

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
| Source | `test/03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Software Interrupts ARM64 (SVC)
- Software Interrupts x86_64 (INT/SYSCALL)
- Software Interrupts RISC-V 32 (ECALL)
- Software Interrupts RISC-V 64 (ECALL)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
