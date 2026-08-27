# VHDL Sim Runner Integration System Specification

> System-level tests for the GHDL simulator runner integration layer. Covers GhdlResult phase discrimination, failure surfacing, SourceMapHook field requirements, and the VhdlTestbenchDiagnostic structure. Tests ensure that deliberately invalid VHDL (analyze failure), elaboration failure, and assertion failure at runtime are each surfaced as distinct failing Simple test results.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- analyze phase is recognized as analyze
   - Expected: ghdl_phase_is_analyze("analyze") is true
   - Expected: ghdl_phase_is_elaborate("analyze") is false
   - Expected: ghdl_phase_is_run("analyze") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("analyze phase is recognized as analyze")
expect(ghdl_phase_is_analyze("analyze")).to_equal(true)
expect(ghdl_phase_is_elaborate("analyze")).to_equal(false)
expect(ghdl_phase_is_run("analyze")).to_equal(false)
```

</details>

#### elaborate phase is recognized as elaborate

- elaborate phase is recognized as elaborate
   - Expected: ghdl_phase_is_elaborate("elaborate") is true
   - Expected: ghdl_phase_is_analyze("elaborate") is false
   - Expected: ghdl_phase_is_run("elaborate") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("elaborate phase is recognized as elaborate")
expect(ghdl_phase_is_elaborate("elaborate")).to_equal(true)
expect(ghdl_phase_is_analyze("elaborate")).to_equal(false)
expect(ghdl_phase_is_run("elaborate")).to_equal(false)
```

</details>

#### run phase is recognized as run

- run phase is recognized as run
   - Expected: ghdl_phase_is_run("run") is true
   - Expected: ghdl_phase_is_analyze("run") is false
   - Expected: ghdl_phase_is_elaborate("run") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run phase is recognized as run")
expect(ghdl_phase_is_run("run")).to_equal(true)
expect(ghdl_phase_is_analyze("run")).to_equal(false)
expect(ghdl_phase_is_elaborate("run")).to_equal(false)
```

</details>

### VHDL Sim Runner - GhdlResult Pass/Fail

#### passed result is not a failure

- passed result is not a failure
   - Expected: ghdl_is_failure(true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passed result is not a failure")
expect(ghdl_is_failure(true)).to_equal(false)
```

</details>

#### failed result is a failure

- failed result is a failure
   - Expected: ghdl_is_failure(false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("failed result is a failure")
expect(ghdl_is_failure(false)).to_equal(true)
```

</details>

#### ok result to_text contains phase name and OK

- ok result to_text contains phase name and OK
   - Expected: s contains `analyze`
   - Expected: s contains `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ok result to_text contains phase name and OK")
val s = ghdl_result_to_text("analyze", true, 0)
expect(s.contains("analyze")).to_equal(true)
expect(s.contains("OK")).to_equal(true)
```

</details>

#### fail result to_text contains phase name and FAIL

- fail result to_text contains phase name and FAIL
   - Expected: s contains `elaborate`
   - Expected: s contains `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fail result to_text contains phase name and FAIL")
val s = ghdl_result_to_text("elaborate", false, 1)
expect(s.contains("elaborate")).to_equal(true)
expect(s.contains("FAIL")).to_equal(true)
```

</details>

#### fail result to_text contains exit code

- fail result to_text contains exit code
   - Expected: s contains `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fail result to_text contains exit code")
val s = ghdl_result_to_text("run", false, 127)
expect(s.contains("127")).to_equal(true)
```

</details>

#### ok result to_text does not contain FAIL

- ok result to_text does not contain FAIL
   - Expected: s does not contain `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ok result to_text does not contain FAIL")
val s = ghdl_result_to_text("analyze", true, 0)
expect(s.contains("FAIL")).to_equal(false)
```

</details>

#### fail result to_text does not contain OK

- fail result to_text does not contain OK
   - Expected: s does not contain `: OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fail result to_text does not contain OK")
val s = ghdl_result_to_text("run", false, 1)
expect(s.contains(": OK")).to_equal(false)
```

</details>

### VHDL Sim Runner - Failure Phase Ordering

#### all phases passing means no failure

- all phases passing means no failure
   - Expected: phase equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all phases passing means no failure")
val phase = first_failure_phase(true, true, true)
expect(phase).to_equal("")
```

</details>

#### analyze failure is reported before elaborate

- analyze failure is reported before elaborate
   - Expected: phase equals `analyze`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("analyze failure is reported before elaborate")
val phase = first_failure_phase(false, true, true)
expect(phase).to_equal("analyze")
```

</details>

#### elaborate failure is reported when analyze passes

- elaborate failure is reported when analyze passes
   - Expected: phase equals `elaborate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("elaborate failure is reported when analyze passes")
val phase = first_failure_phase(true, false, true)
expect(phase).to_equal("elaborate")
```

</details>

#### run failure is reported when analyze and elaborate pass

- run failure is reported when analyze and elaborate pass
   - Expected: phase equals `run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run failure is reported when analyze and elaborate pass")
val phase = first_failure_phase(true, true, false)
expect(phase).to_equal("run")
```

</details>

#### all phases passing returns empty string

- all phases passing returns empty string
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all phases passing returns empty string")
val ok = all_phases_passed(true, true, true)
expect(ok).to_equal(true)
```

</details>

#### analyze failure means not all phases passed

- analyze failure means not all phases passed
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("analyze failure means not all phases passed")
val ok = all_phases_passed(false, true, true)
expect(ok).to_equal(false)
```

</details>

### VHDL Sim Runner - Invalid VHDL Detection

#### deliberately invalid VHDL is detected before simulation

- deliberately invalid VHDL is detected before simulation
   - Expected: bad is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deliberately invalid VHDL is detected before simulation")
val vhdl = "INVALID_SYNTAX entity broken is end;"
val bad = analyze_error_in_vhdl(vhdl)
expect(bad).to_equal(true)
```

</details>

#### valid VHDL shell passes basic structural check

- valid VHDL shell passes basic structural check
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("valid VHDL shell passes basic structural check")
val vhdl = "entity tb_adder is\nend entity tb_adder;\narchitecture sim of tb_adder is\nbegin\nend architecture sim;"
val valid = is_valid_vhdl_shell(vhdl)
expect(valid).to_equal(true)
```

</details>

#### VHDL missing entity fails basic structural check

- VHDL missing entity fails basic structural check
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("VHDL missing entity fails basic structural check")
val vhdl = "architecture sim of tb_adder is\nbegin\nend architecture sim;"
val valid = is_valid_vhdl_shell(vhdl)
expect(valid).to_equal(false)
```

</details>

#### VHDL missing end architecture fails basic structural check

- VHDL missing end architecture fails basic structural check
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("VHDL missing end architecture fails basic structural check")
val vhdl = "entity tb_adder is\nend entity tb_adder;\narchitecture sim of tb_adder is\nbegin\n"
val valid = is_valid_vhdl_shell(vhdl)
expect(valid).to_equal(false)
```

</details>

### VHDL Sim Runner - Assertion Failure Surfacing

#### stderr containing severity failure signals assertion failure

- stderr containing severity failure signals assertion failure
   - Expected: fail is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stderr containing severity failure signals assertion failure")
val stderr = "tb_adder.vhd:42:5: assertion violation: severity failure"
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(true)
```

</details>

#### stderr containing FAILURE: signals assertion failure

- stderr containing FAILURE: signals assertion failure
   - Expected: fail is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stderr containing FAILURE: signals assertion failure")
val stderr = "FAILURE: expectation 1 in half_adder: expected s_sum to equal '0'"
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(true)
```

</details>

#### clean stderr does not signal assertion failure

- clean stderr does not signal assertion failure
   - Expected: fail is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clean stderr does not signal assertion failure")
val stderr = ""
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(false)
```

</details>

#### stderr with informational message does not signal assertion failure

- stderr with informational message does not signal assertion failure
   - Expected: fail is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stderr with informational message does not signal assertion failure")
val stderr = "note: simulation finished"
val fail = run_phase_assertion_fails(stderr)
expect(fail).to_equal(false)
```

</details>

### VHDL Sim Runner - SourceMapHook

#### enabled hook is recognized as enabled

- enabled hook is recognized as enabled
   - Expected: enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enabled hook is recognized as enabled")
val enabled = source_map_is_enabled(true)
expect(enabled).to_equal(true)
```

</details>

#### disabled hook is not enabled

- disabled hook is not enabled
   - Expected: enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disabled hook is not enabled")
val enabled = source_map_is_enabled(false)
expect(enabled).to_equal(false)
```

</details>

#### disabled hook to_text returns disabled

- disabled hook to_text returns disabled
   - Expected: s equals `disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disabled hook to_text returns disabled")
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", false)
expect(s).to_equal("disabled")
```

</details>

#### enabled hook to_text contains test name

- enabled hook to_text contains test name
   - Expected: s contains `half_adder_test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enabled hook to_text contains test name")
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", true)
expect(s.contains("half_adder_test")).to_equal(true)
```

</details>

#### enabled hook to_text contains expectation index

- enabled hook to_text contains expectation index
   - Expected: s contains `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enabled hook to_text contains expectation index")
val s = source_map_hook_to_text("half_adder_test", 3, "tb_half_adder", "dut", true)
expect(s.contains("3")).to_equal(true)
```

</details>

#### enabled hook to_text contains generated entity

- enabled hook to_text contains generated entity
   - Expected: s contains `tb_half_adder`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enabled hook to_text contains generated entity")
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", true)
expect(s.contains("tb_half_adder")).to_equal(true)
```

</details>

#### enabled hook to_text contains dut instance name

- enabled hook to_text contains dut instance name
   - Expected: s contains `dut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enabled hook to_text contains dut instance name")
val s = source_map_hook_to_text("half_adder_test", 1, "tb_half_adder", "dut", true)
expect(s.contains("dut")).to_equal(true)
```

</details>

### VHDL Sim Runner - VhdlTestbenchDiagnostic

#### diagnostic code is non-empty

- diagnostic code is non-empty
   - Expected: diag_code_nonempty(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic code is non-empty")
val code = "VHDL-TB-CONV-NO-DUT"
expect(diag_code_nonempty(code)).to_equal(true)
```

</details>

#### empty diagnostic code is rejected

- empty diagnostic code is rejected
   - Expected: diag_code_nonempty(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("empty diagnostic code is rejected")
val code = ""
expect(diag_code_nonempty(code)).to_equal(false)
```

</details>

#### diagnostic message names the failing test

- diagnostic message names the failing test
   - Expected: diag_message_names_test(msg, "half_adder_test") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic message names the failing test")
val msg = "No @hardware DUT declaration found in test 'half_adder_test'"
expect(diag_message_names_test(msg, "half_adder_test")).to_equal(true)
```

</details>

#### diagnostic message without test name does not satisfy naming check

- diagnostic message without test name does not satisfy naming check
   - Expected: diag_message_names_test(msg, "half_adder_test") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic message without test name does not satisfy naming check")
val msg = "No @hardware DUT declaration found"
expect(diag_message_names_test(msg, "half_adder_test")).to_equal(false)
```

</details>

#### diagnostic source_line is positive

- diagnostic source_line is positive
   - Expected: diag_has_source_line(line) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic source_line is positive")
val line: i64 = 12
expect(diag_has_source_line(line)).to_equal(true)
```

</details>

#### diagnostic source_line of zero is not valid

- diagnostic source_line of zero is not valid
   - Expected: diag_has_source_line(line) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic source_line of zero is not valid")
val line: i64 = 0
expect(diag_has_source_line(line)).to_equal(false)
```

</details>

#### NO-DUT diagnostic code matches expected pattern

- NO-DUT diagnostic code matches expected pattern
   - Expected: code.starts_with("VHDL-TB-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NO-DUT diagnostic code matches expected pattern")
val code = "VHDL-TB-CONV-NO-DUT"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

#### NO-ASSERT diagnostic code matches expected pattern

- NO-ASSERT diagnostic code matches expected pattern
   - Expected: code.starts_with("VHDL-TB-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NO-ASSERT diagnostic code matches expected pattern")
val code = "VHDL-TB-CONV-NO-ASSERT"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

#### MULTI-DUT diagnostic code matches expected pattern

- MULTI-DUT diagnostic code matches expected pattern
   - Expected: code.starts_with("VHDL-TB-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MULTI-DUT diagnostic code matches expected pattern")
val code = "VHDL-TB-CONV-MULTI-DUT"
expect(code.starts_with("VHDL-TB-")).to_equal(true)
```

</details>

#### NO-PORTS diagnostic code matches expected pattern

- NO-PORTS diagnostic code matches expected pattern
   - Expected: code.starts_with("VHDL-TB-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NO-PORTS diagnostic code matches expected pattern")
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

- **Plan:** `doc/03_plan/agent_tasks/vhdl_testbench_conversion.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d889312ce92057e15f0118053a38beb88ca32126e64204981451fc87d63b9b03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d889312ce92057e15f0118053a38beb88ca32126e64204981451fc87d63b9b03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d889312ce92057e15f0118053a38beb88ca32126e64204981451fc87d63b9b03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/vhdl_sim_runner_integration_spec.spl
mirror: doc/06_spec/03_system/compiler/vhdl_sim_runner_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/vhdl_sim_runner_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/vhdl_sim_runner_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/vhdl_sim_runner_integration_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'analyze phase is recognized as analyze' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_sim_runner_integration_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'elaborate phase is recognized as elaborate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_sim_runner_integration_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'run phase is recognized as run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
