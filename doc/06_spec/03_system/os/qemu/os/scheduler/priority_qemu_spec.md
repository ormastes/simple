# Priority Qemu Specification

> <details>

<!-- sdn-diagram:id=priority_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=priority_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

priority_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=priority_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Priority Qemu Specification

## Scenarios

### Priority Scheduling ARM64

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

### Priority Scheduling x86_64

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

### Priority Scheduling RISC-V 32

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

### Priority Scheduling RISC-V 64

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/scheduler/priority_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Priority Scheduling ARM64
- Priority Scheduling x86_64
- Priority Scheduling RISC-V 32
- Priority Scheduling RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
