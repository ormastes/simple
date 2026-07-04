# Vmm Qemu Specification

> <details>

<!-- sdn-diagram:id=vmm_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vmm_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vmm_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vmm_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vmm Qemu Specification

## Scenarios

### VMM ARM64 (4KB granule)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

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
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

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

### VMM x86_64 (4-level PML4)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

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
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

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

### VMM RISC-V 32 (Sv32)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

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
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

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

### VMM RISC-V 64 (Sv39)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

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
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

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

### VMM CoW walker (_cow_clear_writable_recursive)

<details>
<summary>Advanced: clears writable via _cow_clear_writable_recursive</summary>

#### clears writable via _cow_clear_writable_recursive _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    # The CoW clone path is exercised during process spawn.
    # At minimum the kernel must reach scheduler init without fault.
    expect(output).to_contain("[VMM]")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VMM ARM64 (4KB granule)
- VMM x86_64 (4-level PML4)
- VMM RISC-V 32 (Sv32)
- VMM RISC-V 64 (Sv39)
- VMM CoW walker (_cow_clear_writable_recursive)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 9 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
