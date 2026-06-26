# Ipc Capability Qemu Specification

> <details>

<!-- sdn-diagram:id=ipc_capability_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_capability_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_capability_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_capability_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Capability Qemu Specification

## Scenarios

### Capability ARM64

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Capability x86_64

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Capability RISC-V 32

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Capability RISC-V 64

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Capability ARM64
- Capability x86_64
- Capability RISC-V 32
- Capability RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
