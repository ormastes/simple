# Synthesis Wrapper VexRiscv-SMP Specification

> Verifies AC-3: synthesis_wrapper generates Vivado TCL that includes VexRiscv-SMP .v sources and enables S_AXI_HP0 for K26 bitstream. Tests that new add_verilog_sources and enable_axi_hp_port methods produce TCL containing expected directives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Synthesis Wrapper VexRiscv-SMP Specification

Verifies AC-3: synthesis_wrapper generates Vivado TCL that includes VexRiscv-SMP .v sources and enables S_AXI_HP0 for K26 bitstream. Tests that new add_verilog_sources and enable_axi_hp_port methods produce TCL containing expected directives.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-3 |
| Source | `test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-3: synthesis_wrapper generates Vivado TCL that includes
VexRiscv-SMP .v sources and enables S_AXI_HP0 for K26 bitstream.
Tests that new add_verilog_sources and enable_axi_hp_port methods
produce TCL containing expected directives.

Covers:
- AC-3 (Vivado 2025.2 TCL contains HP port enable + VexRiscv sources)

## Scenarios

### SynthesisProject add_verilog_sources

#### AC-3: TCL contains add_files directive for .v sources

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-3: TCL contains add_files directive for .v sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains add_files directive for .v sources")
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("add_files")
```

</details>

#### AC-3: TCL contains VexRiscv filename

- AC-3: TCL contains VexRiscv filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains VexRiscv filename")
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("VexRiscv")
```

</details>

#### AC-3: TCL contains .v extension reference

- AC-3: TCL contains .v extension reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains .v extension reference")
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain(".v")
```

</details>

### SynthesisProject enable_axi_hp_port

#### AC-3: TCL contains S_AXI_HP0 enable directive

- AC-3: TCL contains S_AXI_HP0 enable directive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains S_AXI_HP0 enable directive")
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("S_AXI_HP0")
```

</details>

#### AC-3: TCL contains PSU__USE__S_AXI_GP key or HP config

- AC-3: TCL contains PSU__USE__S_AXI_GP key or HP config


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains PSU__USE__S_AXI_GP key or HP config")
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("HP")
```

</details>

### Synthesis TCL base correctness

#### AC-3: TCL contains create_project

- AC-3: TCL contains create_project


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains create_project")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-3: TCL contains K26 part number

- AC-3: TCL contains K26 part number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains K26 part number")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-3: TCL contains launch_runs synth_1

- AC-3: TCL contains launch_runs synth_1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: TCL contains launch_runs synth_1")
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("synth")
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

- **Requirements:** `REQ-3`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-3`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `306345e5e2076c8909818ef57535560dac5279d0fd1c93ce0c7b043c742efdb4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `306345e5e2076c8909818ef57535560dac5279d0fd1c93ce0c7b043c742efdb4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `306345e5e2076c8909818ef57535560dac5279d0fd1c93ce0c7b043c742efdb4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: TCL contains add_files directive for .v sources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: TCL contains VexRiscv filename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: TCL contains .v extension reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
