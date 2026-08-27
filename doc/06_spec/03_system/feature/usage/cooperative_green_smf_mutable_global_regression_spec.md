# Cooperative Green SMF Mutable Global Regression

> This SSpec pins the SMF mutable-global runtime fix that unblocks cooperative-green SMF profile rows. SMF execution must preserve module-level mutable storage and relocate local data symbols against the loaded data/BSS section base, not the code base.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green SMF Mutable Global Regression

This SSpec pins the SMF mutable-global runtime fix that unblocks cooperative-green SMF profile rows. SMF execution must preserve module-level mutable storage and relocate local data symbols against the loaded data/BSS section base, not the code base.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-smf-mutable-global |
| Category | Runtime / SMF / Concurrency |
| Status | Fixed Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the SMF mutable-global runtime fix that unblocks
cooperative-green SMF profile rows. SMF execution must preserve module-level
mutable storage and relocate local data symbols against the loaded data/BSS
section base, not the code base.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the regression contract:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl --mode=interpreter --clean
```

## Examples

- The minimal source uses a module-level mutable `COUNT`.
- Source checking and SMF compilation must succeed.
- Running the SMF artifact exits `0`.
- Exit `42` means mutable global state did not persist across calls.
- Negative or signal-like process status means the loader regressed to the old
  crash path.

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl
Cooperative green SMF mutable global regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Scenarios

### Cooperative green SMF mutable-global regression

#### runs a minimal mutable-global SMF without crashing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs a minimal mutable-global SMF without crashing
- Create the minimal mutable-global fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, mutable_global_fixture_source()) is true
- Check and compile the fixture to SMF
   - Expected: check_code equals `0`
   - Expected: compile_code equals `0`
- Run the SMF artifact as a regression guard
   - Expected: run_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs a minimal mutable-global SMF without crashing")
step("Create the minimal mutable-global fixture")
val (mkdir_stdout, mkdir_stderr, mkdir_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + BUILD_DIR])
expect(process_output(mkdir_stdout, mkdir_stderr).len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, mutable_global_fixture_source())).to_equal(true)

step("Check and compile the fixture to SMF")
val (check_stdout, check_stderr, check_code) = rt_process_run(SIMPLE_BIN, ["check", SOURCE_PATH])
expect(process_output(check_stdout, check_stderr)).to_contain("OK")
expect(check_code).to_equal(0)
val (compile_stdout, compile_stderr, compile_code) = rt_process_run(SIMPLE_BIN, ["compile", SOURCE_PATH, "-o", SMF_PATH])
expect(process_output(compile_stdout, compile_stderr)).to_contain("Compiled")
expect(compile_code).to_equal(0)

step("Run the SMF artifact as a regression guard")
val (run_stdout, run_stderr, run_code) = rt_process_run(SIMPLE_BIN, [SMF_PATH])
expect(process_output(run_stdout, run_stderr).len()).to_be_greater_than(-1)
expect(run_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/05_design/multicore_green.md`
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c725775c8f028357ee6d15b28fce1fd111ebfa7a24f9812ffe88d0efb43ef3a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c725775c8f028357ee6d15b28fce1fd111ebfa7a24f9812ffe88d0efb43ef3a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c725775c8f028357ee6d15b28fce1fd111ebfa7a24f9812ffe88d0efb43ef3a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a minimal mutable-global SMF without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
