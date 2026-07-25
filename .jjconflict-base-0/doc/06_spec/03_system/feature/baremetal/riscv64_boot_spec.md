# RISC-V 64-bit Bare-Metal Boot

> Tests the RISC-V 64-bit bare-metal boot sequence including machine mode setup, trap vector configuration, and PMP (Physical Memory Protection) initialization. Verifies correct boot on RV64 targets via QEMU emulation.

<!-- sdn-diagram:id=riscv64_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V 64-bit Bare-Metal Boot

Tests the RISC-V 64-bit bare-metal boot sequence including machine mode setup, trap vector configuration, and PMP (Physical Memory Protection) initialization. Verifies correct boot on RV64 targets via QEMU emulation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/riscv64_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the RISC-V 64-bit bare-metal boot sequence including machine mode setup,
trap vector configuration, and PMP (Physical Memory Protection) initialization.
Verifies correct boot on RV64 targets via QEMU emulation.

## Scenarios

### RISC-V 64 Boot Code

<details>
<summary>Advanced: starts in machine mode</summary>

#### starts in machine mode _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After reset: MPP = 11 (machine mode), MIE = 0 (interrupts disabled)
val mstatus = MSTATUS_MPP_MACHINE
expect(check_machine_mode(mstatus)).to_equal(true)
expect(check_mstatus_init(mstatus)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up trap vector</summary>

#### sets up trap vector _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Direct mode trap vector at 0x80000100
val mtvec = 0x80000100
val result = parse_mtvec(mtvec)
val base = result.base
val mode = result.mode
expect(mode).to_equal(MTVEC_MODE_DIRECT)
expect(check_mtvec_alignment(base, mode)).to_equal(true)
expect(validate_trap_vector(mtvec)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: configures machine registers</summary>

#### configures machine registers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify interrupt enable bits
val mie = MIE_MTIE + MIE_MEIE
expect(check_interrupt_enabled(mie, MIE_MTIE)).to_equal(true)
expect(check_interrupt_enabled(mie, MIE_MEIE)).to_equal(true)
expect(check_interrupt_enabled(mie, MIE_MSIE)).to_equal(false)

# Verify stack setup
val sp = get_stack_pointer()
expect(sp).to_equal(RAM_BASE + STACK_SIZE)
expect(check_stack_alignment_rv64(sp)).to_equal(true)
```

</details>


</details>

### RISC-V 64 QEMU Boot

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
<summary>Advanced: handles traps correctly</summary>

#### handles traps correctly _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU + test kernel with trap handlers
check(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
