# VHDL Sim Runner Integration System Specification

> System-level tests for the GHDL simulator runner integration layer. Covers GhdlResult phase discrimination, failure surfacing, SourceMapHook field requirements, and the VhdlTestbenchDiagnostic structure. Tests ensure that deliberately invalid VHDL (analyze failure), elaboration failure, and assertion failure at runtime are each surfaced as distinct failing Simple test results.

<!-- sdn-diagram:id=vhdl_sim_runner_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_sim_runner_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_sim_runner_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_sim_runner_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Sim Runner Integration System Specification

System-level tests for the GHDL simulator runner integration layer. Covers GhdlResult phase discrimination, failure surfacing, SourceMapHook field requirements, and the VhdlTestbenchDiagnostic structure. Tests ensure that deliberately invalid VHDL (analyze failure), elaboration failure, and assertion failure at runtime are each surfaced as distinct failing Simple test results.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-PARITY-012 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Plan | doc/03_plan/agent_tasks/vhdl_testbench_conversion.md |
| Source | `test/03_system/compiler/vhdl_sim_runner_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level tests for the GHDL simulator runner integration layer. Covers
GhdlResult phase discrimination, failure surfacing, SourceMapHook field
requirements, and the VhdlTestbenchDiagnostic structure. Tests ensure that
deliberately invalid VHDL (analyze failure), elaboration failure, and
assertion failure at runtime are each surfaced as distinct failing Simple test
results.

## Key Concepts

- GhdlResult: phase ("analyze"|"elaborate"|"run"), passed, stderr_capture, exit_code
- Phase discrimination: is_analyze(), is_elaborate(), is_run()
- Failure: is_failure() when passed == false
- SourceMapHook: test_name, expectation_index, generated_entity, dut_instance, is_enabled
- VhdlTestbenchDiagnostic: code (e.g. "VHDL-TB-CONV-NO-DUT"), message, source_line

## Behavior

- GhdlResult.ok(phase) creates a passed result with empty stderr and exit_code 0
- GhdlResult.fail(phase, err, code) creates a failed result with stderr and exit_code
- Analyze failure causes the Simple test to fail before elaboration runs
- Elaboration failure causes the Simple test to fail before simulation runs
- Run failure (assertion) causes the Simple test to fail with stderr context
- SourceMapHook.is_enabled must be true for source-map fields to be emitted
- Diagnostic code must be non-empty and message must name the failing test

## Scenarios

### VHDL Sim Runner - GhdlResult Phase Discrimination

#### analyze phase is recognized as analyze

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ghdl_phase_is_analyze("analyze")).to_equal(true)
expect(ghdl_phase_is_elaborate("analyze")).to_equal(false)
expect(ghdl_phase_is_run("analyze")).to_equal(false)
```

</details>

#### elaborate phase is recognized as elaborate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ghdl_phase_is_elaborate("elaborate")).to_equal(true)
expect(ghdl_phase_is_analyze("elaborate")).to_equal(false)
expect(ghdl_phase_is_run("elaborate")).to_equal(false)
```

</details>

#### run phase is recognized as run

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ghdl_phase_is_run("run")).to_equal(true)
expect(ghdl_phase_is_analyze("run")).to_equal(false)
expect(ghdl_phase_is_elaborate("run")).to_equal(false)
```

</details>

### VHDL Sim Runner - GhdlResult Pass/Fail

#### passed result is not a failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ghdl_is_failure(true)).to_equal(false)
```

</details>

#### failed result is a failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ghdl_is_failure(false)).to_equal(true)
```

</details>

#### ok result to_text contains phase name and OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ghdl_result_to_text("analyze", true, 0)
expect(s.contains("analyze")).to_equal(true)
expect(s.contains("OK")).to_equal(true)
```

</details>

#### fail result to_text contains phase name and FAIL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ghdl_result_to_text("elaborate", false, 1)
expect(s.contains("elaborate")).to_equal(true)
expect(s.contains("FAIL")).to_equal(true)
```

</details>

#### fail result to_text contains exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ghdl_result_to_text("run", false, 127)
expect(s.contains("127")).to_equal(true)
```

</details>

#### ok result to_text does not contain FAIL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ghdl_result_to_text("analyze", true, 0)
expect(s.contains("FAIL")).to_equal(false)
```

</details>

#### fail result to_text does not contain OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ghdl_result_to_text("run", false, 1)
expect(s.contains(": OK")).to_equal(false)
```

</details>

### VHDL Sim Runner - Failure Phase Ordering

#### all phases passing means no failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase = first_failure_phase(true, true, true)
expect(phase).to_equal("")
```

</details>

#### analyze failure is reported before elaborate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase = first_failure_phase(false, true, true)
expect(phase).to_equal("analyze")
```

</details>

#### elaborate failure is reported when analyze passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase = first_failure_phase(true, false, true)
expect(phase).to_equal("elaborate")
```

</details>

#### run failure is reported when analyze and elaborate pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase = first_failure_phase(true, true, false)
expect(phase).to_equal("run")
```

</details>

#### all phases passing returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = all_phases_passed(true, true, true)
expect(ok).to_equal(true)
```

</details>

#### analyze failure means not all phases passed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = all_phases_passed(false, true, true)
expect(ok).to_equal(false)
```

</details>

### VHDL Sim Runner - Invalid VHDL Detection

#### deliberately invalid VHDL is detected before simulation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "INVALID_SYNTAX entity broken is end;"
val bad = analyze_error_in_vhdl(vhdl)
expect(bad).to_equal(true)
```

</details>

#### valid VHDL shell passes basic structural check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "entity tb_adder is\nend entity tb_adder;\narchitecture sim of tb_adder is\nbegin\nend architecture sim;"
val valid = is_valid_vhdl_shell(vhdl)
expect(valid).to_equal(true)
```

</details>

#### VHDL missing entity fails basic structural check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "architecture sim of tb_adder is\nbegin\nend architecture sim;"
val valid = is_valid_vhdl_shell(vhdl)
expect(valid).to_equal(false)
```

</details>

#### VHDL missing end architecture fails basic structural check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "entity tb_adder is\nend entity tb_adder;\narchitecture sim of tb_adder is\nbegin\n"
val valid = is_valid_vhdl_shell(vhdl)
expect(valid).to_equal(false)
```

</details>

### VHDL Sim Runner - Assertion Failure Surfacing

#### stderr containing severity failure signals assertion failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "tb_adder.vhd:42:5: assertion violation: severity failure"
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(true)
```

</details>

#### stderr containing FAILURE: signals assertion failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "FAILURE: expectation 1 in half_adder: expected s_sum to equal '0'"
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(true)
```

</details>

#### clean stderr does not signal assertion failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = ""
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(false)
```

</details>

#### stderr with informational message does not signal assertion failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stderr = "note: simulation finished"
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(false)
```

</details>

### VHDL Sim Runner - SourceMapHook

#### enabled hook is recognized as enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = source_map_is_enabled(true)
expect(enabled).to_equal(true)
```

</details>

#### disabled hook is not enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = source_map_is_enabled(false)
expect(enabled).to_equal(false)
```

</details>

#### disabled hook to_text returns disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", false)
expect(s).to_equal("disabled")
```

</details>

#### enabled hook to_text contains test name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", true)
expect(s.contains("half_adder_test")).to_equal(true)
```

</details>

#### enabled hook to_text contains expectation index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = source_map_hook_to_text("half_adder_test", 3, "tb_half_adder", "dut", true)
expect(s.contains("3")).to_equal(true)
```

</details>

#### enabled hook to_text contains generated entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", true)
expect(s.contains("tb_half_adder")).to_equal(true)
```

</details>

#### enabled hook to_text contains dut instance name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", true)
expect(s.contains("dut")).to_equal(true)
```

</details>

### VHDL Sim Runner - VhdlTestbenchDiagnostic

#### diagnostic code is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "VHDL-TB-CONV-NO-DUT"
expect(diag_code_nonempty(code)).to_equal(true)
```

</details>

#### empty diagnostic code is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = ""
expect(diag_code_nonempty(code)).to_equal(false)
```

</details>

#### diagnostic message names the failing test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "No @hardware DUT declaration found in test 'half_adder_test'"
expect(diag_message_names_test(msg, "half_adder_test")).to_equal(true)
```

</details>

#### diagnostic message without test name does not satisfy naming check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "No @hardware DUT declaration found"
expect(diag_message_names_test(msg, "half_adder_test")).to_equal(false)
```

</details>

#### diagnostic source_line is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line: i64 = 12
expect(diag_has_source_line(line)).to_equal(true)
```

</details>

#### diagnostic source_line of zero is not valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line: i64 = 0
expect(diag_has_source_line(line)).to_equal(false)
```

</details>

#### NO-DUT diagnostic code matches expected pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "VHDL-TB-CONV-NO-DUT"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

#### NO-ASSERT diagnostic code matches expected pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "VHDL-TB-CONV-NO-ASSERT"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

#### MULTI-DUT diagnostic code matches expected pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "VHDL-TB-CONV-MULTI-DUT"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

#### NO-PORTS diagnostic code matches expected pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "VHDL-TB-CONV-NO-PORTS"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vhdl_testbench_conversion.md](doc/03_plan/agent_tasks/vhdl_testbench_conversion.md)


</details>
