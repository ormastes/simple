# Boot Smoke Qemu Specification

> <details>

<!-- sdn-diagram:id=boot_smoke_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=boot_smoke_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

boot_smoke_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=boot_smoke_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Smoke Qemu Specification

## Scenarios

### ARM64 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes PL011 UART</summary>

#### initializes PL011 UART _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: reports memory map</summary>

#### reports memory map _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("[PASS] boot_and_init")
```

</details>


</details>

### x86_64 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes COM1 serial</summary>

#### initializes COM1 serial _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: enumerates PCI devices</summary>

#### enumerates PCI devices _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[pcimgr]")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[stage1] PASS")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("TEST PASSED")
```

</details>


</details>

### RISC-V 32 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes UART via SBI</summary>

#### initializes UART via SBI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: reports memory map</summary>

#### reports memory map _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("[PASS] boot_and_init")
```

</details>


</details>

### RISC-V 64 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes UART via SBI</summary>

#### initializes UART via SBI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: reports memory map</summary>

#### reports memory map _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("[PASS] boot_and_init")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM64 Boot Smoke Tests
- x86_64 Boot Smoke Tests
- RISC-V 32 Boot Smoke Tests
- RISC-V 64 Boot Smoke Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 20 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
