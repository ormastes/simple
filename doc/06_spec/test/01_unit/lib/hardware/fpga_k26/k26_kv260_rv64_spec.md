# KV260 RV64GC FPGA Cross-Validation Specification

> Cross-validates that K26 XDC constraint port names match the VHDL entity port names from generate_soc_top_vhdl_rv64(). Verifies K26 default config sanity, XDC format, Vivado TCL K26 targeting, and SoC VHDL entity completeness for the rv64-ghdl-fpga-boot pipeline.

<!-- sdn-diagram:id=k26_kv260_rv64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=k26_kv260_rv64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

k26_kv260_rv64_spec -> std
k26_kv260_rv64_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=k26_kv260_rv64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# KV260 RV64GC FPGA Cross-Validation Specification

Cross-validates that K26 XDC constraint port names match the VHDL entity port names from generate_soc_top_vhdl_rv64(). Verifies K26 default config sanity, XDC format, Vivado TCL K26 targeting, and SoC VHDL entity completeness for the rv64-ghdl-fpga-boot pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | rv64-ghdl-fpga-boot |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | REQ-1, REQ-6, REQ-7, REQ-9 |
| Research | N/A |
| Source | `test/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Cross-validates that K26 XDC constraint port names match the VHDL
entity port names from generate_soc_top_vhdl_rv64(). Verifies K26
default config sanity, XDC format, Vivado TCL K26 targeting, and
SoC VHDL entity completeness for the rv64-ghdl-fpga-boot pipeline.

Covers:
- AC-1 (VHDL gen produces soc_top_64 + peripherals)
- AC-6 (Vivado TCL targets K26 part)
- AC-7 (XDC validated against GHDL entity port names)
- AC-9 (boot guide sections — tool-verified)

## Compiled-Mode Notes

All checks are text-pattern based and interpreter-safe.
AC-2,3,4 (GHDL), AC-5 (backend bugs), AC-6 (synthesis),
AC-8 (FPGA boot) are tool-verified outside SPipe.

## Scenarios

### KV260 XDC-VHDL Port Cross-Validation

#### AC-7: both XDC and VHDL reference uart_tx port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("uart_tx")
expect(vhdl).to_contain("uart_tx")
```

</details>

#### AC-7: both XDC and VHDL reference uart_rx port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("uart_rx")
expect(vhdl).to_contain("uart_rx")
```

</details>

#### AC-7: both XDC and VHDL reference rst port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("rst")
expect(vhdl).to_contain("rst")
```

</details>

#### AC-7: both XDC and VHDL reference clk

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("clk")
expect(vhdl).to_contain("clk")
```

</details>

#### AC-7: XDC contains JTAG debug port constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("jtag_tck")
expect(xdc).to_contain("jtag_tms")
expect(xdc).to_contain("jtag_tdi")
expect(xdc).to_contain("jtag_tdo")
```

</details>

### K26 Default Config

#### AC-7: default config has 100 MHz clock

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = k26_default_config()
expect(cfg.clock_freq).to_equal(100000000)
```

</details>

#### AC-7: default config uses LVCMOS33 IO standard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = k26_default_config()
expect(cfg.io_standard).to_equal("LVCMOS33")
```

</details>

#### AC-7: default config has UART TX pin H12

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = k26_default_config()
expect(cfg.uart_tx_pin).to_equal("H12")
```

</details>

#### AC-7: default config has UART RX pin E10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = k26_default_config()
expect(cfg.uart_rx_pin).to_equal("E10")
```

</details>

#### AC-7: default config has reset pin G11

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = k26_default_config()
expect(cfg.reset_pin).to_equal("G11")
```

</details>

#### AC-7: default config has 4 LED pins

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = k26_default_config()
val count = cfg.led_pins.len()
expect(count).to_equal(4)
```

</details>

### K26 XDC Format

#### AC-7: XDC contains PACKAGE_PIN assignments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("PACKAGE_PIN")
```

</details>

#### AC-7: XDC contains IOSTANDARD property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("IOSTANDARD")
```

</details>

#### AC-7: XDC contains set_property commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("set_property")
```

</details>

#### AC-7: XDC contains K26 SOM header comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xdc = k26_generate_xdc()
expect(xdc).to_contain("xck26-sfvc784-2LV-c")
```

</details>

### VHDL Gen SoC Entity Completeness

#### AC-1: soc_top_rv64 entity name present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("soc_top_rv64")
```

</details>

#### AC-1: entity contains rv64gc_core instantiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rv64gc_core")
```

</details>

#### AC-1: entity contains CLINT peripheral

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_clint")
```

</details>

#### AC-1: entity contains PLIC peripheral

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_plic")
```

</details>

#### AC-1: entity contains UART peripheral

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_uart")
```

</details>

#### AC-1: entity uses 64-bit Wishbone bus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("63 downto 0")
```

</details>

### Vivado TCL K26 Targeting

#### AC-6: TCL sets K26 FPGA part

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-6: TCL creates Vivado project

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-6: TCL includes bitstream generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("write_bitstream")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-1, REQ-6, REQ-7, REQ-9](REQ-1, REQ-6, REQ-7, REQ-9)


</details>
