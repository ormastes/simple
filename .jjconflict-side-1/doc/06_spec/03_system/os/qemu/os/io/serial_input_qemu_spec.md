# Serial Input Qemu Specification

> <details>

<!-- sdn-diagram:id=serial_input_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serial_input_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serial_input_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serial_input_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Input Qemu Specification

## Scenarios

### Serial Input ARM64

<details>
<summary>Advanced: UART receive path initialized</summary>

#### UART receive path initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

### Serial Input x86_64

<details>
<summary>Advanced: COM1 receive path initialized</summary>

#### COM1 receive path initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

### Serial Input RISC-V 32

<details>
<summary>Advanced: UART receive path initialized</summary>

#### UART receive path initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

### Serial Input RISC-V 64

<details>
<summary>Advanced: UART receive path initialized</summary>

#### UART receive path initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/03_system/os/qemu/os/io/serial_input_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Serial Input ARM64
- Serial Input x86_64
- Serial Input RISC-V 32
- Serial Input RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
