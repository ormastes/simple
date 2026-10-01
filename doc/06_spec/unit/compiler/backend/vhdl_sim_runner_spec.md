# VHDL Simulation Runner Unit Tests

> Unit tests for VhdlSimRunner orchestrator and configuration.

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
| Source | `test/unit/compiler/backend/vhdl_sim_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for VhdlSimRunner orchestrator and configuration.

## Scenarios

### VhdlSimRunner

#### creates with default GHDL config

- creates with default GHDL config
   - Expected: check.ok.? or check.err != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with default GHDL config")
"""
**Given:** VhdlSimRunner.with_ghdl()
**Then:** Runner is configured for GHDL simulation
"""
val runner = VhdlSimRunner.with_ghdl()
val check = runner.check_simulator()
# Either OK or error with install instructions
expect(check.ok.? or check.err != nil).to_equal(true)
```

</details>

#### creates from VhdlEmulationConfig

- creates from VhdlEmulationConfig
   - Expected: check.ok.? or check.err != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from VhdlEmulationConfig")
"""
**Given:** Explicit VhdlEmulationConfig
**Then:** Runner reflects all config settings
"""
val config = VhdlEmulationConfig.ghdl_default()
val runner = VhdlSimRunner.create(config)
val check = runner.check_simulator()
expect(check.ok.? or check.err != nil).to_equal(true)
```

</details>

#### returns error for missing VHDL file

- returns error for missing VHDL file
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for missing VHDL file")
"""
**Given:** Path to non-existent file
**When:** simulate_vhdl_file() called
**Then:** Returns error with file path
"""
val runner = VhdlSimRunner.with_ghdl()
val result = runner.simulate_vhdl_file("/nonexistent/file.vhd", "test")
expect(result.success).to_equal(false)
expect(result.errors.len()).to_be_greater_than(0)
```

</details>

### VhdlEmulationResult

#### creates error result

- creates error result
   - Expected: r.success is false
   - Expected: r.errors.len() equals `1`
   - Expected: r.errors[0] equals `test error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error result")
"""
**Given:** Error message
**Then:** success is false and errors list populated
"""
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e0c8ea4f17156ddd14184a6efb45e729f5f0f93074cddc3c5c5364f4c20d937`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e0c8ea4f17156ddd14184a6efb45e729f5f0f93074cddc3c5c5364f4c20d937`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e0c8ea4f17156ddd14184a6efb45e729f5f0f93074cddc3c5c5364f4c20d937`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/backend/vhdl_sim_runner_spec.spl
mirror: doc/06_spec/unit/compiler/backend/vhdl_sim_runner_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/vhdl_sim_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/vhdl_sim_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/vhdl_sim_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/vhdl_sim_runner_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with default GHDL config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_sim_runner_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates from VhdlEmulationConfig' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_sim_runner_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error for missing VHDL file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
