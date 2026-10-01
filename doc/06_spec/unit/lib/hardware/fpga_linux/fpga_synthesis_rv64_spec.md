# FPGA Synthesis and Constraints Specification (RV64)

> Tests for FPGA synthesis pipeline: XDC constraint generation for Kria K26 (clock, UART TX/RX, reset, JTAG), Vivado TCL script generation with correct FPGA part, and VHDL source inclusion.

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
| Source | `test/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-12
# @req REQ-13
```

</details>

#### AC-4: XDC contains clock constraint

- AC-4: XDC contains clock constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: XDC contains clock constraint")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("create_clock")
```

</details>

#### AC-4: XDC contains UART TX pin

- AC-4: XDC contains UART TX pin


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: XDC contains UART TX pin")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("uart_tx")
```

</details>

#### AC-4: XDC contains UART RX pin

- AC-4: XDC contains UART RX pin


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: XDC contains UART RX pin")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("uart_rx")
```

</details>

#### AC-4: XDC contains reset pin

- AC-4: XDC contains reset pin


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: XDC contains reset pin")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("rst")
```

</details>

#### AC-4: XDC contains JTAG pin constraint

- AC-4: XDC contains JTAG pin constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: XDC contains JTAG pin constraint")
val xdc = k26_generate_xdc()
expect(xdc).to_contain("jtag")
```

</details>

### XDC Generator

#### AC-4: xdc_gen produces valid XDC format

- AC-4: xdc_gen produces valid XDC format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: xdc_gen produces valid XDC format")
val xdc = generate_xdc_constraints()
expect(xdc).to_contain("set_property")
```

</details>

#### AC-4: xdc_gen includes PACKAGE_PIN assignments

- AC-4: xdc_gen includes PACKAGE_PIN assignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: xdc_gen includes PACKAGE_PIN assignments")
val xdc = generate_xdc_constraints()
expect(xdc).to_contain("PACKAGE_PIN")
```

</details>

#### AC-4: xdc_gen includes IOSTANDARD

- AC-4: xdc_gen includes IOSTANDARD


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: xdc_gen includes IOSTANDARD")
val xdc = generate_xdc_constraints()
expect(xdc).to_contain("IOSTANDARD")
```

</details>

### Synthesis Wrapper TCL

#### AC-5: synthesis TCL contains create_project

- AC-5: synthesis TCL contains create_project


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL contains create_project")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-5: synthesis TCL contains add_files for VHDL sources

- AC-5: synthesis TCL contains add_files for VHDL sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL contains add_files for VHDL sources")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("add_files")
```

</details>

#### AC-5: synthesis TCL sets correct FPGA part for K26

- AC-5: synthesis TCL sets correct FPGA part for K26


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL sets correct FPGA part for K26")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-5: synthesis TCL sets top entity

- AC-5: synthesis TCL sets top entity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL sets top entity")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("set_property top")
```

</details>

#### AC-5: synthesis TCL launches synthesis run

- AC-5: synthesis TCL launches synthesis run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL launches synthesis run")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("launch_runs synth_1")
```

</details>

#### AC-5: synthesis TCL launches implementation run

- AC-5: synthesis TCL launches implementation run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL launches implementation run")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("launch_runs impl_1")
```

</details>

#### AC-5: synthesis TCL generates bitstream

- AC-5: synthesis TCL generates bitstream


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL generates bitstream")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("write_bitstream")
```

</details>

#### AC-5: synthesis TCL includes XDC constraint file

- AC-5: synthesis TCL includes XDC constraint file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL includes XDC constraint file")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain(".xdc")
```

</details>

#### AC-5: synthesis TCL includes RV64 core VHDL source

- AC-5: synthesis TCL includes RV64 core VHDL source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: synthesis TCL includes RV64 core VHDL source")
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

- **Requirements:** `REQ-12, REQ-13`
- **Research:** `doc/01_research/domain/riscv_fpga_linux.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-12`
- `REQ-13`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96730dde7a35f2271e16ffeeb8cf000570eb31ea9c141460e60b45bcb9423539`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96730dde7a35f2271e16ffeeb8cf000570eb31ea9c141460e60b45bcb9423539`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96730dde7a35f2271e16ffeeb8cf000570eb31ea9c141460e60b45bcb9423539`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl
mirror: doc/06_spec/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'AC-4: k26_xdc generates constraint text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: XDC contains clock constraint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: XDC contains UART TX pin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: XDC contains UART RX pin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
