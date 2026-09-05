# FV2 RISC-V Dual-Track Readiness

> This system specification verifies the exact RVFI readiness boundary hardened

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FV2 RISC-V Dual-Track Readiness

This system specification verifies the exact RVFI readiness boundary hardened

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This system specification verifies the exact RVFI readiness boundary hardened
for REQ-FV2-015 and REQ-FV2-019. Synthetic cores exercise checker behavior;
they never count as RTL proof. Product acceptance additionally requires the
aggregate Lean/BYL sidecar gate and the strict SymbiYosys proof gate.

## Scenarios

### FV2 RISC-V dual-track readiness

#### should accept exactly the canonical 21-port RVFI readiness manifest

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Readiness checker contract (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FV2-015
# @req REQ-FV2-019.
```

</details>

#### should reject an RVFI core missing an extended control port

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed interface mutations (expected show, folded, detail, or skip)


- should reject an RVFI core missing an extended control port
- Remove the rvfi_mode control port from the canonical fixture
- Confirm the checker rejects the incomplete RVFI interface
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an RVFI core missing an extended control port")
step("Remove the rvfi_mode control port from the canonical fixture")
val core_path = prepare_readiness_fixture(
    "missing_rvfi_mode_core", "rvfi_mode")

step("Confirm the checker rejects the incomplete RVFI interface")
val (stdout, stderr, code) = run_readiness(core_path)
val report = stdout + stderr
expect(code).to_equal(1)
expect(report).to_contain("RVFI readiness: missing RVFI ports")
expect(report).to_contain("rvfi_mode")
expect(report).to_contain(
    "ERROR: RVFI formal flow requires all RVFI ports")
expect(report.contains("READY:")).to_be(false)
```

</details>

#### should reject a missing generated core instead of reporting readiness

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Missing-artifact rejection (expected show, folded, detail, or skip)


- should reject a missing generated core instead of reporting readiness
- Present a missing generated RVFI core path
- Confirm missing Stage-4 artifacts remain blocked
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a missing generated core instead of reporting readiness")
step("Present a missing generated RVFI core path")
expect(dir_create_all(TOOL_DIR)).to_be(true)
val missing_path = ARTIFACT_DIR + "/missing_generated_core.vhd"

step("Confirm missing Stage-4 artifacts remain blocked")
val (stdout, stderr, code) = run_readiness(missing_path)
val report = stdout + stderr
expect(code).to_equal(1)
expect(report).to_contain("ERROR: RV32I core VHDL not found")
expect(report.contains("READY:")).to_be(false)
```

</details>

#### should keep all four extended RVFI port omissions fail closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Checker mutation calibration (expected show, folded, detail, or skip)


- should keep all four extended RVFI port omissions fail closed
- Run the readiness checker's deliberate-red mutation matrix
- Confirm every omitted control port was rejected
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep all four extended RVFI port omissions fail closed")
step("Run the readiness checker's deliberate-red mutation matrix")
val (stdout, stderr, code) = process_run_timeout(
    "/bin/sh", [RVFI_CHECK, "--self-test"], 30000)
val report = stdout + stderr

step("Confirm every omitted control port was rejected")
expect(code).to_equal(0)
expect(report).to_contain(
    "STATUS: PASS rvfi-formal-readiness self-test")
expect(report.contains("STATUS: FAIL")).to_be(false)
```

</details>

#### should pass the aggregate generated and manual RISC-V proof-model gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Qualified dual-track execution (expected show, folded, detail, or skip)


- should pass the aggregate generated and manual RISC-V proof-model gate
   - Log capture: after_step
- Run the dual-track aggregate proof gate
   - Log capture: after_step
- Require the generated sidecar and durable manual proof layers
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pass the aggregate generated and manual RISC-V proof-model gate")
step("Run the dual-track aggregate proof gate")
val (stdout, stderr, code) = process_run_timeout(
    "/bin/sh", [DUAL_TRACK_CHECK], 600000)
val report = stdout + stderr

step("Require the generated sidecar and durable manual proof layers")
expect(code).to_equal(0)
expect(report).to_contain("STATUS: PASS riscv-formal-dual-track")
expect(report.contains("STATUS: FAIL")).to_be(false)
```

</details>

#### should require a strict SymbiYosys proof pass after readiness

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Qualified dual-track execution (expected show, folded, detail, or skip)


- should require a strict SymbiYosys proof pass after readiness
   - Log capture: after_step
- Run the strict RVFI SymbiYosys proof gate
   - Log capture: after_step
- Reject readiness-only or missing-artifact evidence
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require a strict SymbiYosys proof pass after readiness")
step("Run the strict RVFI SymbiYosys proof gate")
val (stdout, stderr, code) = process_run_timeout(
    "/bin/sh", [STRICT_SBY_CHECK], 600000)
val report = stdout + stderr

step("Reject readiness-only or missing-artifact evidence")
expect(code).to_equal(0)
expect(report).to_contain("STATUS: PASS riscv-rtl-sby-proof")
expect(report.contains("STATUS: FAIL")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FV2-015`
- `REQ-FV2-019.`
- `REQ-SSPEC-SYSTEM.`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdd679c36cf951cd825f73e76d8fbeef5e03ff3a8c3ce47b520efe878d17b71c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdd679c36cf951cd825f73e76d8fbeef5e03ff3a8c3ce47b520efe878d17b71c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdd679c36cf951cd825f73e76d8fbeef5e03ff3a8c3ce47b520efe878d17b71c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl
mirror: doc/06_spec/03_system/compiler/fv2_riscv_dual_track_readiness_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/03_system/compiler/fv2_riscv_dual_track_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/fv2_riscv_dual_track_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:65:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should accept exactly the canonical 21-port RVFI readiness manifest' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept exactly the canonical 21-port RVFI readiness manifest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an RVFI core missing an extended control port' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an RVFI core missing an extended control port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a missing generated core instead of reporting readiness' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a missing generated core instead of reporting readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep all four extended RVFI port omissions fail closed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep all four extended RVFI port omissions fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass the aggregate generated and manual RISC-V proof-model gate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl:160:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require a strict SymbiYosys proof pass after readiness' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
