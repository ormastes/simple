# Full Consistency Qemu Specification

> <details>

<!-- sdn-diagram:id=full_consistency_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=full_consistency_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

full_consistency_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=full_consistency_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Full Consistency Qemu Specification

## Scenarios

### Full Cross-Architecture Consistency

<details>
<summary>Advanced: all architectures print SimpleOS banner</summary>

#### all architectures print SimpleOS banner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: all architectures initialize PMM</summary>

#### all architectures initialize PMM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures initialize interrupts</summary>

#### all architectures initialize interrupts _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures initialize timer</summary>

#### all architectures initialize timer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[TIMER]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures create scheduler tasks</summary>

#### all architectures create scheduler tasks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures pass 5 boot tests</summary>

#### all architectures pass 5 boot tests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("passed=5 failed=0")
```

</details>


</details>

<details>
<summary>Advanced: all architectures complete test suite</summary>

#### all architectures complete test suite _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("SimpleOS Tests Complete")
```

</details>


</details>

<details>
<summary>Advanced: no architecture reports failures</summary>

#### no architecture reports failures _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        val has_fail = output.contains("[FAIL]")
        expect(has_fail).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Full Cross-Architecture Consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
