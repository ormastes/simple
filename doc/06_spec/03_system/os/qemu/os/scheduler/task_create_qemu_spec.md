# Task Create Qemu Specification

> <details>

<!-- sdn-diagram:id=task_create_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_create_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_create_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_create_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Create Qemu Specification

## Scenarios

### Task Creation ARM64

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

### Task Creation x86_64

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

### Task Creation RISC-V 32

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

### Task Creation RISC-V 64

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Task Creation ARM64
- Task Creation x86_64
- Task Creation RISC-V 32
- Task Creation RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 12 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
