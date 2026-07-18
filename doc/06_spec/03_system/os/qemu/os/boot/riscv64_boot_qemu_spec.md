# Riscv64 Boot Qemu Specification

> <details>

<!-- sdn-diagram:id=riscv64_boot_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_boot_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_boot_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_boot_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Boot Qemu Specification

## Scenarios

### RISC-V 64 Architecture Boot

<details>
<summary>Advanced: UART initialized via SBI</summary>

#### UART initialized via SBI _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("UART")
```

</details>


</details>

<details>
<summary>Advanced: prints RISC-V 64 architecture identifier</summary>

#### prints RISC-V 64 architecture identifier _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("RISC-V 64")
```

</details>


</details>

<details>
<summary>Advanced: memory map parsed</summary>

#### memory map parsed _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: OpenSBI S-mode entry</summary>

#### OpenSBI S-mode entry _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("SBI")
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes</summary>

#### boot sequence completes _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("boot complete")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V 64 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
