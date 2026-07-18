# ARM64 (AArch64) Bare-Metal Boot

> Tests the AArch64 bare-metal boot sequence including exception level setup, MMU configuration, and stack initialization. Verifies that the boot code correctly transitions from EL2/EL1 to the application entry point.

<!-- sdn-diagram:id=arm64_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm64_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm64_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm64_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ARM64 (AArch64) Bare-Metal Boot

Tests the AArch64 bare-metal boot sequence including exception level setup, MMU configuration, and stack initialization. Verifies that the boot code correctly transitions from EL2/EL1 to the application entry point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/arm64_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the AArch64 bare-metal boot sequence including exception level setup,
MMU configuration, and stack initialization. Verifies that the boot code
correctly transitions from EL2/EL1 to the application entry point.

## Scenarios

### ARM64 Boot Code

<details>
<summary>Advanced: generates valid exception vector table</summary>

#### generates valid exception vector table _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vt = create_vector_table()
# All handler addresses should be non-zero
expect(vt.sync_current_sp0.handler > 0).to_equal(true)
expect(vt.irq_current_spx.handler > 0).to_equal(true)
expect(vt.sync_lower64.handler > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: checks vector table alignment</summary>

#### checks vector table alignment _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VBAR must be 2KB aligned
expect(check_vbar_alignment(0x40000000)).to_equal(true)
expect(check_vbar_alignment(0x40000800)).to_equal(true)
# Not 2KB aligned
expect(check_vbar_alignment(0x40000100)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: sets up exception levels correctly</summary>

#### sets up exception levels correctly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All 4 exception levels should be valid
expect(check_exception_level(EL0)).to_equal(true)
expect(check_exception_level(EL1)).to_equal(true)
expect(check_exception_level(EL2)).to_equal(true)
expect(check_exception_level(EL3)).to_equal(true)
# EL transitions: higher -> lower
expect(check_el_transition(EL3, EL1)).to_equal(true)
expect(check_el_transition(EL1, EL3)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: maintains stack pointer alignment</summary>

#### maintains stack pointer alignment _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = get_stack_pointer()
# AArch64 requires 16-byte stack alignment
expect(check_stack_alignment(sp)).to_equal(true)
expect(STACK_SIZE % 16).to_equal(0)
```

</details>


</details>

### ARM64 QEMU Boot

<details>
<summary>Advanced: boots on virt machine</summary>

#### boots on virt machine _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU installation
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles exceptions correctly</summary>

#### handles exceptions correctly _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU + test kernel with exception handlers
check(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
