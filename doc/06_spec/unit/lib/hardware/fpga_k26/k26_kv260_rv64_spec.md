# KV260 RV64GC FPGA Cross-Validation Specification

> Cross-validates that K26 XDC constraint port names match the VHDL entity port names from generate_soc_top_vhdl_rv64(). Verifies K26 default config sanity, XDC format, Vivado TCL K26 targeting, and SoC VHDL entity completeness for the rv64-ghdl-fpga-boot pipeline.

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
| Source | `test/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-7: both XDC and VHDL reference uart_tx port


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: both XDC and VHDL reference uart_tx port")
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("uart_tx")
expect(vhdl).to_contain("uart_tx")
```

</details>

#### AC-7: both XDC and VHDL reference uart_rx port

- AC-7: both XDC and VHDL reference uart_rx port


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: both XDC and VHDL reference uart_rx port")
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("uart_rx")
expect(vhdl).to_contain("uart_rx")
```

</details>

#### AC-7: both XDC and VHDL reference rst port

- AC-7: both XDC and VHDL reference rst port


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: both XDC and VHDL reference rst port")
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("rst")
expect(vhdl).to_contain("rst")
```

</details>

#### AC-7: both XDC and VHDL reference clk

- AC-7: both XDC and VHDL reference clk


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: both XDC and VHDL reference clk")
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("clk")
expect(vhdl).to_contain("clk")
```

</details>

#### AC-7: XDC contains JTAG debug port constraints

- AC-7: XDC contains JTAG debug port constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: XDC contains JTAG debug port constraints")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("jtag_tck")
expect(xdc).to_contain("jtag_tms")
expect(xdc).to_contain("jtag_tdi")
expect(xdc).to_contain("jtag_tdo")
```

</details>

### K26 Default Config

#### AC-7: default config has 100 MHz clock

- AC-7: default config has 100 MHz clock
   - Expected: cfg.clock_freq equals `100000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: default config has 100 MHz clock")
val cfg = k26_default_config()
expect(cfg.clock_freq).to_equal(100000000)
```

</details>

#### AC-7: default config uses LVCMOS33 IO standard

- AC-7: default config uses LVCMOS33 IO standard
   - Expected: cfg.io_standard equals `LVCMOS33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: default config uses LVCMOS33 IO standard")
val cfg = k26_default_config()
expect(cfg.io_standard).to_equal("LVCMOS33")
```

</details>

#### AC-7: default config has UART TX pin H12

- AC-7: default config has UART TX pin H12
   - Expected: cfg.uart_tx_pin equals `H12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: default config has UART TX pin H12")
val cfg = k26_default_config()
expect(cfg.uart_tx_pin).to_equal("H12")
```

</details>

#### AC-7: default config has UART RX pin E10

- AC-7: default config has UART RX pin E10
   - Expected: cfg.uart_rx_pin equals `E10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: default config has UART RX pin E10")
val cfg = k26_default_config()
expect(cfg.uart_rx_pin).to_equal("E10")
```

</details>

#### AC-7: default config has reset pin G11

- AC-7: default config has reset pin G11
   - Expected: cfg.reset_pin equals `G11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: default config has reset pin G11")
val cfg = k26_default_config()
expect(cfg.reset_pin).to_equal("G11")
```

</details>

#### AC-7: default config has 4 LED pins

- AC-7: default config has 4 LED pins
   - Expected: count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: default config has 4 LED pins")
val cfg = k26_default_config()
val count = cfg.led_pins.len()
expect(count).to_equal(4)
```

</details>

### K26 XDC Format

#### AC-7: XDC contains PACKAGE_PIN assignments

- AC-7: XDC contains PACKAGE_PIN assignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: XDC contains PACKAGE_PIN assignments")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("PACKAGE_PIN")
```

</details>

#### AC-7: XDC contains IOSTANDARD property

- AC-7: XDC contains IOSTANDARD property


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: XDC contains IOSTANDARD property")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("IOSTANDARD")
```

</details>

#### AC-7: XDC contains set_property commands

- AC-7: XDC contains set_property commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: XDC contains set_property commands")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("set_property")
```

</details>

#### AC-7: XDC contains K26 SOM header comment

- AC-7: XDC contains K26 SOM header comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: XDC contains K26 SOM header comment")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("xck26-sfvc784-2LV-c")
```

</details>

### VHDL Gen SoC Entity Completeness

#### AC-1: soc_top_rv64 entity name present

- AC-1: soc_top_rv64 entity name present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: soc_top_rv64 entity name present")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("soc_top_rv64")
```

</details>

#### AC-1: entity contains rv64gc_core instantiation

- AC-1: entity contains rv64gc_core instantiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: entity contains rv64gc_core instantiation")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rv64gc_core")
```

</details>

#### AC-1: entity contains CLINT peripheral

- AC-1: entity contains CLINT peripheral


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: entity contains CLINT peripheral")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_clint")
```

</details>

#### AC-1: entity contains PLIC peripheral

- AC-1: entity contains PLIC peripheral


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: entity contains PLIC peripheral")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_plic")
```

</details>

#### AC-1: entity contains UART peripheral

- AC-1: entity contains UART peripheral


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: entity contains UART peripheral")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_uart")
```

</details>

#### AC-1: entity uses 64-bit Wishbone bus

- AC-1: entity uses 64-bit Wishbone bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: entity uses 64-bit Wishbone bus")
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("63 downto 0")
```

</details>

### Vivado TCL K26 Targeting

#### AC-6: TCL sets K26 FPGA part

- AC-6: TCL sets K26 FPGA part


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: TCL sets K26 FPGA part")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-6: TCL creates Vivado project

- AC-6: TCL creates Vivado project


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: TCL creates Vivado project")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-6: TCL includes bitstream generation

- AC-6: TCL includes bitstream generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: TCL includes bitstream generation")
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

- **Requirements:** `REQ-1, REQ-6, REQ-7, REQ-9`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-1`
- `REQ-6`
- `REQ-7`
- `REQ-9`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20dfc8575d8d76e2312f048865a55de67304824d14177859198b30d7521c0ae1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20dfc8575d8d76e2312f048865a55de67304824d14177859198b30d7521c0ae1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20dfc8575d8d76e2312f048865a55de67304824d14177859198b30d7521c0ae1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl
mirror: doc/06_spec/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: both XDC and VHDL reference uart_tx port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: both XDC and VHDL reference uart_rx port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: both XDC and VHDL reference rst port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
