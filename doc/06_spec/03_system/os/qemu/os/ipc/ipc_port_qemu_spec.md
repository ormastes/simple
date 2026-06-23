# Ipc Port Qemu Specification

> <details>

<!-- sdn-diagram:id=ipc_port_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_port_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_port_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_port_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Port Qemu Specification

## Scenarios

### IPC Port ARM64

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu_cached(Architecture.Arm64)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu_cached(Architecture.Arm64)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port x86_64

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu_cached(Architecture.X86_64)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu_cached(Architecture.X86_64)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port x86_32

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86):
    val output = _run_qemu_cached(Architecture.X86)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86):
    val output = _run_qemu_cached(Architecture.X86)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port RISC-V 32

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu_cached(Architecture.Riscv32)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu_cached(Architecture.Riscv32)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port RISC-V 64

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu_cached(Architecture.Riscv64)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu_cached(Architecture.Riscv64)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC Port ARM64
- IPC Port x86_64
- IPC Port x86_32
- IPC Port RISC-V 32
- IPC Port RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
