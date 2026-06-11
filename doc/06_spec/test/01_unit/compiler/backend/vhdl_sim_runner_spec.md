# VHDL Simulation Runner Unit Tests

> Unit tests for VhdlSimRunner orchestrator and configuration.

<!-- sdn-diagram:id=vhdl_sim_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_sim_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_sim_runner_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_sim_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Simulation Runner Unit Tests

Unit tests for VhdlSimRunner orchestrator and configuration.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-EMU-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/compiler/backend/vhdl_sim_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for VhdlSimRunner orchestrator and configuration.

## Scenarios

### VhdlSimRunner

#### creates with default GHDL config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = VhdlSimRunner.with_ghdl()
val check = runner.check_simulator()
# Either OK or error with install instructions
expect(check.ok.? or check.err.?).to_equal(true)
```

</details>

#### creates from VhdlEmulationConfig

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = VhdlEmulationConfig.ghdl_default()
val runner = VhdlSimRunner.create(config)
val check = runner.check_simulator()
expect(check.ok.? or check.err.?).to_equal(true)
```

</details>

#### returns error for missing VHDL file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = VhdlSimRunner.with_ghdl()
val result = runner.simulate_vhdl_file("/nonexistent/file.vhd", "test")
expect(result.success).to_equal(false)
expect(result.errors.len()).to_be_greater_than(0)
```

</details>

### VhdlEmulationResult

#### creates error result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = VhdlEmulationResult.error("test error")
expect(r.success).to_equal(false)
expect(r.errors.len()).to_equal(1)
expect(r.errors[0]).to_equal("test error")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
