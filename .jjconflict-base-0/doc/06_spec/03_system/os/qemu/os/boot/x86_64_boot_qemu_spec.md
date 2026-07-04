# X86 64 Boot Qemu Specification

> <details>

<!-- sdn-diagram:id=x86_64_boot_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_boot_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_boot_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_boot_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Boot Qemu Specification

## Scenarios

### x86_64 Architecture Boot

<details>
<summary>Advanced: COM1 serial initialized at 0x3F8</summary>

#### COM1 serial initialized at 0x3F8 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("serial")
```

</details>


</details>

<details>
<summary>Advanced: prints x86_64 architecture identifier</summary>

#### prints x86_64 architecture identifier _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("x86_64")
```

</details>


</details>

<details>
<summary>Advanced: memory map detected</summary>

#### memory map detected _(slow)_

<details>
<summary>Executable SSpec</summary>

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
<summary>Advanced: GDT loaded</summary>

#### GDT loaded _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("GDT")
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes</summary>

#### boot sequence completes _(slow)_

<details>
<summary>Executable SSpec</summary>

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
| Source | `test/03_system/os/qemu/os/boot/x86_64_boot_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
