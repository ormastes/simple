# Memory Cross Qemu Specification

> <details>

<!-- sdn-diagram:id=memory_cross_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=memory_cross_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

memory_cross_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=memory_cross_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Cross Qemu Specification

## Scenarios

### Memory Cross-Architecture Consistency

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
<summary>Advanced: all architectures report memory initialized</summary>

#### all architectures report memory initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("Memory initialized")
```

</details>


</details>

<details>
<summary>Advanced: all architectures complete memory init pass</summary>

#### all architectures complete memory init pass _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[PASS] memory_init")
```

</details>


</details>

<details>
<summary>Advanced: all architectures report usable memory regions</summary>

#### all architectures report usable memory regions _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("usable")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Memory Cross-Architecture Consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
