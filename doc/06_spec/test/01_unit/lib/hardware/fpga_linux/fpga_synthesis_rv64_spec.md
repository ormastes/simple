# FPGA Synthesis and Constraints Specification (RV64)

> Tests for FPGA synthesis pipeline: XDC constraint generation for Kria K26 (clock, UART TX/RX, reset, JTAG), Vivado TCL script generation with correct FPGA part, and VHDL source inclusion.

<!-- sdn-diagram:id=fpga_synthesis_rv64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fpga_synthesis_rv64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fpga_synthesis_rv64_spec -> std
fpga_synthesis_rv64_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fpga_synthesis_rv64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FPGA Synthesis and Constraints Specification (RV64)

Tests for FPGA synthesis pipeline: XDC constraint generation for Kria K26 (clock, UART TX/RX, reset, JTAG), Vivado TCL script generation with correct FPGA part, and VHDL source inclusion.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-fpga-linux-boot |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | REQ-12, REQ-13 |
| Research | doc/01_research/domain/riscv_fpga_linux.md |
| Source | `test/01_unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for FPGA synthesis pipeline: XDC constraint generation for
Kria K26 (clock, UART TX/RX, reset, JTAG), Vivado TCL script
generation with correct FPGA part, and VHDL source inclusion.

Covers:
- AC-4 (XDC constraints generated for target FPGA board)
- AC-5 (Vivado synthesis completes without critical errors)

## Compiled-Mode Notes

XDC text pattern checks and TCL script content checks are
interpreter-safe. Actual Vivado synthesis (AC-5) requires Vivado
installed and is a hardware-gated test.

## Scenarios

### K26 XDC Constraints

#### AC-4: k26_xdc generates constraint text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
val len = xdc.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-4: XDC contains clock constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("create_clock")
```

</details>

#### AC-4: XDC contains UART TX pin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("uart_tx")
```

</details>

#### AC-4: XDC contains UART RX pin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("uart_rx")
```

</details>

#### AC-4: XDC contains reset pin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("rst")
```

</details>

#### AC-4: XDC contains JTAG pin constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("jtag")
```

</details>

### XDC Generator

#### AC-4: xdc_gen produces valid XDC format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = generate_xdc_constraints()
expect(xdc).to_contain("set_property")
```

</details>

#### AC-4: xdc_gen includes PACKAGE_PIN assignments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = generate_xdc_constraints()
expect(xdc).to_contain("PACKAGE_PIN")
```

</details>

#### AC-4: xdc_gen includes IOSTANDARD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = generate_xdc_constraints()
expect(xdc).to_contain("IOSTANDARD")
```

</details>

### Synthesis Wrapper TCL

#### AC-5: synthesis TCL contains create_project

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-5: synthesis TCL contains add_files for VHDL sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("add_files")
```

</details>

#### AC-5: synthesis TCL sets correct FPGA part for K26

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-5: synthesis TCL sets top entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("set_property top")
```

</details>

#### AC-5: synthesis TCL launches synthesis run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("launch_runs synth_1")
```

</details>

#### AC-5: synthesis TCL launches implementation run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("launch_runs impl_1")
```

</details>

#### AC-5: synthesis TCL generates bitstream

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("write_bitstream")
```

</details>

#### AC-5: synthesis TCL includes XDC constraint file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain(".xdc")
```

</details>

#### AC-5: synthesis TCL includes RV64 core VHDL source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("rv64gc")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-12, REQ-13](REQ-12, REQ-13)
- **Research:** [doc/01_research/domain/riscv_fpga_linux.md](doc/01_research/domain/riscv_fpga_linux.md)


</details>
