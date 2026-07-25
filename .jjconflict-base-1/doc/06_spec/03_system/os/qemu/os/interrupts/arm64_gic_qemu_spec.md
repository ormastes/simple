# Arm64 Gic Qemu Specification

> <details>

<!-- sdn-diagram:id=arm64_gic_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm64_gic_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm64_gic_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm64_gic_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Gic Qemu Specification

## Scenarios

### ARM64 GICv2

<details>
<summary>Advanced: GIC distributor region reserved at 0x08000000</summary>

#### GIC distributor region reserved at 0x08000000 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("0x08000000")
```

</details>


</details>

<details>
<summary>Advanced: interrupt controller initialized</summary>

#### interrupt controller initialized _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: device region marked reserved in memory map</summary>

#### device region marked reserved in memory map _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("device")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/interrupts/arm64_gic_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM64 GICv2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
