# KV260 RV64GC FPGA Cross-Validation Specification

> Verifies the k26 kv260 rv64 behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# KV260 RV64GC FPGA Cross-Validation Specification

Verifies the k26 kv260 rv64 behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the k26 kv260 rv64 behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### KV260 XDC-VHDL Port Cross-Validation

#### AC-7: both XDC and VHDL reference uart_tx port

- Verify: AC-7: both XDC and VHDL reference uart_tx port


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: both XDC and VHDL reference uart_tx port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("uart_tx")
expect(vhdl).to_contain("uart_tx")
```

</details>

#### AC-7: both XDC and VHDL reference uart_rx port

- Verify: AC-7: both XDC and VHDL reference uart_rx port


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: both XDC and VHDL reference uart_rx port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("uart_rx")
expect(vhdl).to_contain("uart_rx")
```

</details>

#### AC-7: both XDC and VHDL reference rst port

- Verify: AC-7: both XDC and VHDL reference rst port


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: both XDC and VHDL reference rst port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("rst")
expect(vhdl).to_contain("rst")
```

</details>

#### AC-7: both XDC and VHDL reference clk

- Verify: AC-7: both XDC and VHDL reference clk


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: both XDC and VHDL reference clk")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
val vhdl = generate_soc_top_vhdl_rv64()
expect(xdc).to_contain("clk")
expect(vhdl).to_contain("clk")
```

</details>

#### AC-7: XDC contains JTAG debug port constraints

- Verify: AC-7: XDC contains JTAG debug port constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: XDC contains JTAG debug port constraints")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
expect(xdc).to_contain("jtag_tck")
expect(xdc).to_contain("jtag_tms")
expect(xdc).to_contain("jtag_tdi")
expect(xdc).to_contain("jtag_tdo")
```

</details>

### K26 Default Config

#### AC-7: default config has 100 MHz clock

- Verify: AC-7: default config has 100 MHz clock
   - Expected: cfg.clock_freq equals `100000000)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: default config has 100 MHz clock")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = k26_default_config()
expect(cfg.clock_freq).to_equal(100000000)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-7: default config uses LVCMOS33 IO standard

- Verify: AC-7: default config uses LVCMOS33 IO standard
   - Expected: cfg.io_standard equals `LVCMOS33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: default config uses LVCMOS33 IO standard")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = k26_default_config()
expect(cfg.io_standard).to_equal("LVCMOS33")
```

</details>

#### AC-7: default config has UART TX pin H12

- Verify: AC-7: default config has UART TX pin H12
   - Expected: cfg.uart_tx_pin equals `H12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: default config has UART TX pin H12")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = k26_default_config()
expect(cfg.uart_tx_pin).to_equal("H12")
```

</details>

#### AC-7: default config has UART RX pin E10

- Verify: AC-7: default config has UART RX pin E10
   - Expected: cfg.uart_rx_pin equals `E10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: default config has UART RX pin E10")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = k26_default_config()
expect(cfg.uart_rx_pin).to_equal("E10")
```

</details>

#### AC-7: default config has reset pin G11

- Verify: AC-7: default config has reset pin G11
   - Expected: cfg.reset_pin equals `G11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: default config has reset pin G11")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = k26_default_config()
expect(cfg.reset_pin).to_equal("G11")
```

</details>

#### AC-7: default config has 4 LED pins

- Verify: AC-7: default config has 4 LED pins
   - Expected: count equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: default config has 4 LED pins")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = k26_default_config()
val count = cfg.led_pins.len()
expect(count).to_equal(4)  # oracle: pinned constant asserted by this scenario
```

</details>

### K26 XDC Format

#### AC-7: XDC contains PACKAGE_PIN assignments

- Verify: AC-7: XDC contains PACKAGE_PIN assignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: XDC contains PACKAGE_PIN assignments")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
expect(xdc).to_contain("PACKAGE_PIN")
```

</details>

#### AC-7: XDC contains IOSTANDARD property

- Verify: AC-7: XDC contains IOSTANDARD property


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: XDC contains IOSTANDARD property")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
expect(xdc).to_contain("IOSTANDARD")
```

</details>

#### AC-7: XDC contains set_property commands

- Verify: AC-7: XDC contains set_property commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: XDC contains set_property commands")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
expect(xdc).to_contain("set_property")
```

</details>

#### AC-7: XDC contains K26 SOM header comment

- Verify: AC-7: XDC contains K26 SOM header comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-7: XDC contains K26 SOM header comment")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val xdc = k26_generate_xdc()
expect(xdc).to_contain("xck26-sfvc784-2LV-c")
```

</details>

### VHDL Gen SoC Entity Completeness

#### AC-1: soc_top_rv64 entity name present

- Verify: AC-1: soc_top_rv64 entity name present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-1: soc_top_rv64 entity name present")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("soc_top_rv64")
```

</details>

#### AC-1: entity contains rv64gc_core instantiation

- Verify: AC-1: entity contains rv64gc_core instantiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-1: entity contains rv64gc_core instantiation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("rv64gc_core")
```

</details>

#### AC-1: entity contains CLINT peripheral

- Verify: AC-1: entity contains CLINT peripheral


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-1: entity contains CLINT peripheral")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_clint")
```

</details>

#### AC-1: entity contains PLIC peripheral

- Verify: AC-1: entity contains PLIC peripheral


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-1: entity contains PLIC peripheral")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_plic")
```

</details>

#### AC-1: entity contains UART peripheral

- Verify: AC-1: entity contains UART peripheral


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-1: entity contains UART peripheral")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("u_uart")
```

</details>

#### AC-1: entity uses 64-bit Wishbone bus

- Verify: AC-1: entity uses 64-bit Wishbone bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-1: entity uses 64-bit Wishbone bus")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val vhdl = generate_soc_top_vhdl_rv64()
expect(vhdl).to_contain("63 downto 0")
```

</details>

### Vivado TCL K26 Targeting

#### AC-6: TCL sets K26 FPGA part

- Verify: AC-6: TCL sets K26 FPGA part


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-6: TCL sets K26 FPGA part")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-6: TCL creates Vivado project

- Verify: AC-6: TCL creates Vivado project


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-6: TCL creates Vivado project")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-6: TCL includes bitstream generation

- Verify: AC-6: TCL includes bitstream generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-6 REQ-7 REQ-9
step("Verify: AC-6: TCL includes bitstream generation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d778b4bacdf47e17ffa3feb0c2eb4c64547863f0198d02c884805ec56ccf2867`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d778b4bacdf47e17ffa3feb0c2eb4c64547863f0198d02c884805ec56ccf2867`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d778b4bacdf47e17ffa3feb0c2eb4c64547863f0198d02c884805ec56ccf2867`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
