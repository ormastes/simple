# Combined Stress Qemu Specification

> <details>

<!-- sdn-diagram:id=combined_stress_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=combined_stress_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

combined_stress_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=combined_stress_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Combined Stress Qemu Specification

## Scenarios

### Combined Stress ARM64

<details>
<summary>Advanced: kernel runs all subsystems to completion</summary>

#### kernel runs all subsystems to completion _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("SimpleOS Tests Complete")
```

</details>


</details>

### Combined Stress x86_64

<details>
<summary>Advanced: kernel runs all subsystems to completion</summary>

#### kernel runs all subsystems to completion _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("SimpleOS Tests Complete")
```

</details>


</details>

### Combined Stress RISC-V 32

<details>
<summary>Advanced: kernel runs all subsystems to completion</summary>

#### kernel runs all subsystems to completion _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("SimpleOS Tests Complete")
```

</details>


</details>

### Combined Stress RISC-V 64

<details>
<summary>Advanced: kernel runs all subsystems to completion</summary>

#### kernel runs all subsystems to completion _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("SimpleOS Tests Complete")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/stress/combined_stress_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Combined Stress ARM64
- Combined Stress x86_64
- Combined Stress RISC-V 32
- Combined Stress RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
