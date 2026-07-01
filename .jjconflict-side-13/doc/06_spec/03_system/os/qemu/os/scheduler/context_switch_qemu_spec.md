# Context Switch Qemu Specification

> <details>

<!-- sdn-diagram:id=context_switch_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_switch_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_switch_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_switch_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Switch Qemu Specification

## Scenarios

### Context Switch ARM64

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

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

### Context Switch x86_64

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

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

### Context Switch RISC-V 32

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

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

### Context Switch RISC-V 64

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

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
| Source | `test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Context Switch ARM64
- Context Switch x86_64
- Context Switch RISC-V 32
- Context Switch RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
