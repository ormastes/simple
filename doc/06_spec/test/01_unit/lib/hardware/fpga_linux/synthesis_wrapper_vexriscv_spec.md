# Synthesis Wrapper VexRiscv-SMP Specification

> Verifies AC-3: synthesis_wrapper generates Vivado TCL that includes VexRiscv-SMP .v sources and enables S_AXI_HP0 for K26 bitstream. Tests that new add_verilog_sources and enable_axi_hp_port methods produce TCL containing expected directives.

<!-- sdn-diagram:id=synthesis_wrapper_vexriscv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=synthesis_wrapper_vexriscv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

synthesis_wrapper_vexriscv_spec -> std
synthesis_wrapper_vexriscv_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=synthesis_wrapper_vexriscv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("add_files")
```

</details>

#### AC-3: TCL contains VexRiscv filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("VexRiscv")
```

</details>

#### AC-3: TCL contains .v extension reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain(".v")
```

</details>

### SynthesisProject enable_axi_hp_port

#### AC-3: TCL contains S_AXI_HP0 enable directive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("S_AXI_HP0")
```

</details>

#### AC-3: TCL contains PSU__USE__S_AXI_GP key or HP config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = tcl_with_vexriscv()
expect(tcl).to_contain("HP")
```

</details>

### Synthesis TCL base correctness

#### AC-3: TCL contains create_project

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("create_project")
```

</details>

#### AC-3: TCL contains K26 part number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tcl = generate_vivado_tcl_rv64()
expect(tcl).to_contain("xck26")
```

</details>

#### AC-3: TCL contains launch_runs synth_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [REQ-3](REQ-3)


</details>
