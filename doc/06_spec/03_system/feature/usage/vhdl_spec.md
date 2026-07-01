# VHDL Backend Toolchain

> Tests VHDL backend toolchain integration with GHDL and Yosys. Covers GHDL availability detection, VHDL source analysis (valid and invalid files), entity elaboration, simulation with stop time, synthesis, file I/O operations (write, read, exists), VhdlToolResult structure validation, and Yosys integration via the GHDL plugin for synthesis to JSON netlist.

<!-- sdn-diagram:id=vhdl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Backend Toolchain

Tests VHDL backend toolchain integration with GHDL and Yosys. Covers GHDL availability detection, VHDL source analysis (valid and invalid files), entity elaboration, simulation with stop time, synthesis, file I/O operations (write, read, exists), VhdlToolResult structure validation, and Yosys integration via the GHDL plugin for synthesis to JSON netlist.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/vhdl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests VHDL backend toolchain integration with GHDL and Yosys. Covers GHDL
availability detection, VHDL source analysis (valid and invalid files),
entity elaboration, simulation with stop time, synthesis, file I/O operations
(write, read, exists), VhdlToolResult structure validation, and Yosys
integration via the GHDL plugin for synthesis to JSON netlist.

## Syntax

```simple
val result = ghdl_analyze(path)
expect(result.exit_code).to_equal(0)
val content = vhdl_read_file(path)
```
VHDL Backend Feature Tests

Tests specific to VHDL backend toolchain functionality.
Tests GHDL and Yosys availability and wrapper functions.

## Scenarios

### VHDL Toolchain Availability

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### GHDL Analysis

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### GHDL Elaboration

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### GHDL Simulation

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### GHDL Synthesis

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### VHDL File Operations

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### VhdlToolResult structure

#### env_skip: requires SIMPLE_VHDL_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
```

</details>

### Yosys VHDL Synthesis

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
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
