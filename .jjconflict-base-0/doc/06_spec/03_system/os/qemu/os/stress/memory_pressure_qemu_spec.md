# Memory Pressure Qemu Specification

> <details>

<!-- sdn-diagram:id=memory_pressure_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=memory_pressure_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

memory_pressure_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=memory_pressure_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Pressure Qemu Specification

## Scenarios

### Memory Pressure ARM64

<details>
<summary>Advanced: kernel boots with full memory subsystem</summary>

#### kernel boots with full memory subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### Memory Pressure x86_64

<details>
<summary>Advanced: kernel boots with full memory subsystem</summary>

#### kernel boots with full memory subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### Memory Pressure RISC-V 32

<details>
<summary>Advanced: kernel boots with full memory subsystem</summary>

#### kernel boots with full memory subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### Memory Pressure RISC-V 64

<details>
<summary>Advanced: kernel boots with full memory subsystem</summary>

#### kernel boots with full memory subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/stress/memory_pressure_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Memory Pressure ARM64
- Memory Pressure x86_64
- Memory Pressure RISC-V 32
- Memory Pressure RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
