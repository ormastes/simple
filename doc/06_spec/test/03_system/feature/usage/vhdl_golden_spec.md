# VHDL Golden File Tests

> Generates VHDL output from the VhdlBuilder and compares against checked-in reference .vhd golden files for regression testing. Validates counter and ALU entity generation including library headers, entity/architecture blocks, port declarations, signal assignments, clocked processes, and combinational logic. Also performs structural sanity checks on generated VHDL output.

<!-- sdn-diagram:id=vhdl_golden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_golden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_golden_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_golden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Golden File Tests

Generates VHDL output from the VhdlBuilder and compares against checked-in reference .vhd golden files for regression testing. Validates counter and ALU entity generation including library headers, entity/architecture blocks, port declarations, signal assignments, clocked processes, and combinational logic. Also performs structural sanity checks on generated VHDL output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/usage/vhdl_golden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Generates VHDL output from the VhdlBuilder and compares against checked-in
reference .vhd golden files for regression testing. Validates counter and ALU
entity generation including library headers, entity/architecture blocks, port
declarations, signal assignments, clocked processes, and combinational logic.
Also performs structural sanity checks on generated VHDL output.

## Syntax

```simple
var builder = VhdlBuilder__create("counter")
builder.emit_library_header()
builder.emit_entity_begin("counter")
builder.emit_port("clk", "in", mapper.bit_type(), false)
val vhdl = builder.build()
```
VHDL Golden File Tests

Generates VHDL output from the builder and compares against
checked-in reference .vhd files in examples/09_embedded/vhdl/builder/golden/.

## Scenarios

### VHDL Golden File Tests

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### VHDL Golden Output Sanity

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
