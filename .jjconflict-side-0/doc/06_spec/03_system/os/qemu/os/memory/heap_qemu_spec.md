# Heap Qemu Specification

> <details>

<!-- sdn-diagram:id=heap_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=heap_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

heap_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=heap_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Heap Qemu Specification

## Scenarios

### Heap ARM64

<details>
<summary>Advanced: heap allocator initialized from PMM</summary>

#### heap allocator initialized from PMM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: kernel boots with memory subsystem</summary>

#### kernel boots with memory subsystem _(slow)_

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

### Heap x86_64

<details>
<summary>Advanced: heap allocator initialized from PMM</summary>

#### heap allocator initialized from PMM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: kernel boots with memory subsystem</summary>

#### kernel boots with memory subsystem _(slow)_

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

### Heap RISC-V 32

<details>
<summary>Advanced: heap allocator initialized from PMM</summary>

#### heap allocator initialized from PMM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: kernel boots with memory subsystem</summary>

#### kernel boots with memory subsystem _(slow)_

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

### Heap RISC-V 64

<details>
<summary>Advanced: heap allocator initialized from PMM</summary>

#### heap allocator initialized from PMM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: kernel boots with memory subsystem</summary>

#### kernel boots with memory subsystem _(slow)_

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
| Source | `test/03_system/os/qemu/os/memory/heap_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Heap ARM64
- Heap x86_64
- Heap RISC-V 32
- Heap RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
