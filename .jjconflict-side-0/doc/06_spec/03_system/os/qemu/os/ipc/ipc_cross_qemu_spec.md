# Ipc Cross Qemu Specification

> <details>

<!-- sdn-diagram:id=ipc_cross_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_cross_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_cross_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_cross_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Cross Qemu Specification

## Scenarios

### IPC Cross-Architecture

<details>
<summary>Advanced: all architectures create IPC tasks</summary>

#### all architectures create IPC tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures register demo tasks</summary>

#### all architectures register demo tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

<details>
<summary>Advanced: all architectures report task creation pass</summary>

#### all architectures report task creation pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/ipc/ipc_cross_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC Cross-Architecture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
