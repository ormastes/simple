# K26 SoC Top VexRiscv-SMP Integration Specification

> Verifies AC-2: k26_soc_top wires VexRiscv-SMP .v + AXI-HP bridge + soc_rtl peripherals (CLINT, PLIC, UART16550). Tests that the generated VHDL/SV top-level text references VexRiscv-SMP, CLINT, PLIC, and UART.

<!-- sdn-diagram:id=k26_soc_top_vexriscv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=k26_soc_top_vexriscv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

k26_soc_top_vexriscv_spec -> std
k26_soc_top_vexriscv_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=k26_soc_top_vexriscv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# K26 SoC Top VexRiscv-SMP Integration Specification

Verifies AC-2: k26_soc_top wires VexRiscv-SMP .v + AXI-HP bridge + soc_rtl peripherals (CLINT, PLIC, UART16550). Tests that the generated VHDL/SV top-level text references VexRiscv-SMP, CLINT, PLIC, and UART.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | REQ-2 |
| Source | `test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-2: k26_soc_top wires VexRiscv-SMP .v + AXI-HP bridge +
soc_rtl peripherals (CLINT, PLIC, UART16550). Tests that the generated
VHDL/SV top-level text references VexRiscv-SMP, CLINT, PLIC, and UART.

Covers:
- AC-2 (SOC integration: core wired to CLINT+PLIC+UART16550)

## Scenarios

### K26VexRiscvSocConfig

#### AC-2: default config hart_count is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_soc_config()
expect(cfg.hart_count).to_equal(1)
```

</details>

#### AC-2: default config axi_data_width is 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_soc_config()
expect(cfg.axi_data_width).to_equal(128)
```

</details>

### K26 SoC Top VexRiscv-SMP Wiring

#### AC-2: generated text contains VexRiscv reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = soc_top_sv()
expect(sv).to_contain("VexRiscv")
```

</details>

#### AC-2: generated text references CLINT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = soc_top_sv()
expect(sv).to_contain("clint")
```

</details>

#### AC-2: generated text references PLIC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = soc_top_sv()
expect(sv).to_contain("plic")
```

</details>

#### AC-2: generated text references UART

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = soc_top_sv()
expect(sv).to_contain("uart")
```

</details>

#### AC-2: generated text references AXI HP bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = soc_top_sv()
expect(sv).to_contain("HP0")
```

</details>

#### AC-2: generated text is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = soc_top_sv()
val len = sv.length()
expect(len).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-2](REQ-2)


</details>
