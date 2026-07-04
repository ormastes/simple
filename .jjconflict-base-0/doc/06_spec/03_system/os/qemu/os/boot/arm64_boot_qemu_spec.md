# Arm64 Boot Qemu Specification

> <details>

<!-- sdn-diagram:id=arm64_boot_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm64_boot_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm64_boot_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm64_boot_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Boot Qemu Specification

## Scenarios

### ARM64 Architecture Boot

<details>
<summary>Advanced: PL011 UART initialized at 0x09000000</summary>

#### PL011 UART initialized at 0x09000000 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("PL011")
```

</details>


</details>

<details>
<summary>Advanced: prints ARM64 architecture identifier</summary>

#### prints ARM64 architecture identifier _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("ARM64")
```

</details>


</details>

<details>
<summary>Advanced: QEMU virt machine memory map detected</summary>

#### QEMU virt machine memory map detected _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("Memory map parsed")
```

</details>


</details>

<details>
<summary>Advanced: kernel region at 0x40000000</summary>

#### kernel region at 0x40000000 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("0x40000000")
```

</details>


</details>

<details>
<summary>Advanced: GICv2 region reserved</summary>

#### GICv2 region reserved _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("device")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM64 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
