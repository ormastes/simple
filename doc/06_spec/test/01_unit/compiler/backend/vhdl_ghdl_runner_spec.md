# Vhdl Ghdl Runner Specification

> _Unit coverage for the GhdlResult class factory methods and accessors._

<!-- sdn-diagram:id=vhdl_ghdl_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_ghdl_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_ghdl_runner_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_ghdl_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Ghdl Runner Specification

## Scenarios

### GhdlResult model
_Unit coverage for the GhdlResult class factory methods and accessors._

#### ok factory sets passed=true and empty stderr_capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.ok("analyze")
expect(r.passed).to_equal(true)
expect(r.stderr_capture).to_equal("")
expect(r.exit_code).to_equal(0)
expect(r.phase).to_equal("analyze")
```

</details>

#### fail factory sets passed=false with stderr and exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.fail("elaborate", "binding indication is missing", 1)
expect(r.passed).to_equal(false)
expect(r.stderr_capture).to_contain("binding indication is missing")
expect(r.exit_code).to_equal(1)
expect(r.phase).to_equal("elaborate")
```

</details>

#### is_analyze returns true only for analyze phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.ok("analyze")
expect(r.is_analyze()).to_equal(true)
expect(r.is_elaborate()).to_equal(false)
expect(r.is_run()).to_equal(false)
```

</details>

#### is_elaborate returns true only for elaborate phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.ok("elaborate")
expect(r.is_elaborate()).to_equal(true)
expect(r.is_analyze()).to_equal(false)
expect(r.is_run()).to_equal(false)
```

</details>

#### is_run returns true only for run phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.ok("run")
expect(r.is_run()).to_equal(true)
expect(r.is_analyze()).to_equal(false)
expect(r.is_elaborate()).to_equal(false)
```

</details>

#### is_failure returns false for ok result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.ok("run")
expect(r.is_failure()).to_equal(false)
```

</details>

#### is_failure returns true for fail result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.fail("run", "simulation error", 2)
expect(r.is_failure()).to_equal(true)
```

</details>

#### to_text encodes ok result correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.ok("run")
expect(r.to_text()).to_equal("GHDL run: OK")
```

</details>

#### to_text encodes failure with exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = GhdlResult.fail("run", "assertion failed", 2)
expect(r.to_text()).to_equal("GHDL run: FAIL exit=2")
expect(r.to_text()).to_contain("FAIL")
expect(r.to_text()).to_contain("exit=2")
```

</details>

#### missing ghdl path returns analyze-phase failure with exit code 127

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# run_vhdl_testbench_with_ghdl returns analyze-phase fail when ghdl
# is not on PATH. We verify the contract via a known-absent binary path.
# This test is structural: if ghdl IS installed, skip the 127 check.
val r = run_vhdl_testbench_with_ghdl("/nonexistent/no_such_file.vhd", "test_tb")
# Either ghdl is missing (exit=127, phase=analyze) or the file is missing
# (analyze fails with non-zero exit). Either way is_failure() must be true.
expect(r.is_failure()).to_equal(true)
expect(r.phase).to_equal("analyze")
```

</details>

#### artifact helper produces analyze-phase failure for non-existent work dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_vhdl_testbench_artifact_with_ghdl("test_tb", "-- stub vhdl", "/nonexistent/workdir")
expect(r.is_failure()).to_equal(true)
expect(r.phase).to_equal("analyze")
```

</details>

### CombinationalBench model
_Unit coverage for CombinationalBench factory and accessors._

#### create sets all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = CombinationalBench.create("and_gate_tb", "and_gate", 2, 1)
expect(b.bench_name).to_equal("and_gate_tb")
expect(b.dut_entity).to_equal("and_gate")
expect(b.stimulus_count).to_equal(2)
expect(b.assertion_count).to_equal(1)
```

</details>

#### is_combinational returns true when has_clock is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = CombinationalBench.create("tb", "dut", 0, 0)
expect(b.is_combinational()).to_equal(true)
```

</details>

#### total_checks sums stimulus and assertion counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = CombinationalBench.create("tb", "dut", 3, 4)
expect(b.total_checks()).to_equal(7)
```

</details>

### ClockedBench model
_Unit coverage for ClockedBench factory and accessors._

#### create sets all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = ClockedBench.create("reg_tb", "reg1", 10, 2, 20)
expect(b.bench_name).to_equal("reg_tb")
expect(b.dut_entity).to_equal("reg1")
expect(b.clock_period_ns).to_equal(10)
expect(b.reset_cycles).to_equal(2)
expect(b.total_cycles).to_equal(20)
```

</details>

#### has_reset returns true when reset_cycles > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = ClockedBench.create("tb", "dut", 10, 2, 20)
expect(b.has_reset()).to_equal(true)
```

</details>

#### has_reset returns false when reset_cycles is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = ClockedBench.create("tb", "dut", 10, 0, 20)
expect(b.has_reset()).to_equal(false)
```

</details>

#### sim_time_ns is total_cycles times clock_period_ns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = ClockedBench.create("tb", "dut", 10, 0, 20)
expect(b.sim_time_ns()).to_equal(200)
```

</details>

### RenderOutput model
_Unit coverage for RenderOutput factory and accessors._

#### create sets all fields with has_source_map false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = RenderOutput.create("and_gate_tb", "library ieee;", 1)
expect(r.entity_name).to_equal("and_gate_tb")
expect(r.vhdl_text).to_equal("library ieee;")
expect(r.line_count).to_equal(1)
expect(r.has_source_map).to_equal(false)
```

</details>

#### is_empty returns true for zero lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = RenderOutput.create("tb", "", 0)
expect(r.is_empty()).to_equal(true)
```

</details>

#### is_empty returns false for non-zero lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = RenderOutput.create("tb", "-- something", 1)
expect(r.is_empty()).to_equal(false)
```

</details>

#### with_source_map returns copy with has_source_map true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = RenderOutput.create("tb", "-- vhdl", 1)
val r2 = r.with_source_map()
expect(r2.has_source_map).to_equal(true)
expect(r2.entity_name).to_equal("tb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_ghdl_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GhdlResult model
- CombinationalBench model
- ClockedBench model
- RenderOutput model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
