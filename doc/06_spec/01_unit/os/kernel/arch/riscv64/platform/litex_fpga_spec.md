# LiteX FPGA Platform Specification

> Verifies AC-6: the litex_fpga platform capsule composes LitexFpgaMemoryMap correctly. Tests that the platform init and UART/timer API exist with the right types and that the composed memory map returns expected constants.

<!-- sdn-diagram:id=litex_fpga_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=litex_fpga_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

litex_fpga_spec -> std
litex_fpga_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=litex_fpga_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LiteX FPGA Platform Specification

Verifies AC-6: the litex_fpga platform capsule composes LitexFpgaMemoryMap correctly. Tests that the platform init and UART/timer API exist with the right types and that the composed memory map returns expected constants.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-6 |
| Source | `test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-6: the litex_fpga platform capsule composes LitexFpgaMemoryMap
correctly. Tests that the platform init and UART/timer API exist with the
right types and that the composed memory map returns expected constants.

Covers:
- AC-6 (Minimal host services: console I/O, timer init, idle loop parameterization)

## Scenarios

### LiteX FPGA Platform

#### AC-6: platform name is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = litex_fpga_platform_name()
val len = name.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-6: platform name contains litex or de10nano

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = litex_fpga_platform_name()
expect(name).to_contain("litex")
```

</details>

### LiteX FPGA Memory Map Composition

#### AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_litex_map()
expect(m.uart_base()).to_equal(4026535936)
```

</details>

#### AC-6: LitexFpgaMemoryMap ram_base is 0x40000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_litex_map()
expect(m.ram_base()).to_equal(1073741824)
```

</details>

#### AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_litex_map()
expect(m.clint_base()).to_equal(4026597376)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-6](REQ-6)


</details>
