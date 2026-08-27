# SMF Runtime-Pool Closure Lookup Regression

> This SSpec pins the wrapper-shaped SMF runtime-pool regression for `multicore_green_spawn`. Profile-generated workloads call a helper such as `spawn_worker() -> multicore_green_spawn(\: worker())`; that helper must compile into the SMF module instead of falling back to `rt_interp_call`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Runtime-Pool Closure Lookup Regression

This SSpec pins the wrapper-shaped SMF runtime-pool regression for `multicore_green_spawn`. Profile-generated workloads call a helper such as `spawn_worker() -> multicore_green_spawn(\: worker())`; that helper must compile into the SMF module instead of falling back to `rt_interp_call`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-smf-runtime-pool-closure |
| Category | Runtime / SMF / Concurrency |
| Status | Fixed |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the wrapper-shaped SMF runtime-pool regression for
`multicore_green_spawn`. Profile-generated workloads call a helper such as
`spawn_worker() -> multicore_green_spawn(\: worker())`; that helper must compile
into the SMF module instead of falling back to `rt_interp_call`.

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
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl --mode=interpreter --clean
```

## Examples

- The fixture compiles to SMF successfully.
- The fixture configures runtime-pool parallelism.
- The wrapper helper executes through compiled SMF code.
- The native runtime pool returns the expected value.
- The process prints `wrapper_smf_pool_pass=true`.

## Regression Shape

The checked profile script generates wrapper helpers so the benchmark can keep
the spawn expression compact and comparable across parallel/fanout sections:

```simple
use std.spec.step

fn worker() -> i64:
    42

fn spawn_worker() -> MulticoreGreenHandle:
    multicore_green_spawn(\: worker())
```

The direct shape below is intentionally not enough regression coverage because
it already passes on this checkout:

```simple
val handle = multicore_green_spawn(\: worker())
```

This spec exercises the wrapper shape because direct submission alone is too
weak: direct `multicore_green_spawn(\: worker())` already passed before this
regression was fixed.

## Expected Runtime Output

The SMF process must print runtime-pool setup evidence and the pass marker:

```text
multicore_green_parallelism = 2/2
got = 42
wrapper_smf_pool_pass=true
```

It must not print:

```text
function not found: spawn_worker
```

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl
SMF runtime-pool closure regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The executable fixture must use `spawn_worker() -> multicore_green_spawn(\: worker())`.
- The fixture must pass before SMF multicore-green profile rows count as M:N evidence.
- The fixture must mention `wrapper_smf_pool_pass=true`.
- The fixture must reject `function not found: spawn_worker`.
- The direct worker shape must not replace this wrapper-shaped regression.

## Scenarios

### SMF runtime-pool closure lookup regression

#### keeps the wrapper-shaped multicore-green SMF path executable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the wrapper-shaped multicore-green SMF path executable
- Write the minimal wrapper-shaped multicore-green fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, regression_fixture_source()) is true
- Compile the fixture to SMF
   - Expected: compile_code equals `0`
   - Expected: exists_code equals `0`
- Run the SMF fixture and require the compiled wrapper path
   - Expected: run_code equals `0`
- Verify the blocker document records the resolved failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the wrapper-shaped multicore-green SMF path executable")
step("Write the minimal wrapper-shaped multicore-green fixture")
val (_mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, regression_fixture_source())).to_equal(true)

step("Compile the fixture to SMF")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " -o " + SMF_PATH)
expect(compile_code).to_equal(0)
val (_exists_out, exists_code) = shell("test -f " + SMF_PATH)
expect(exists_code).to_equal(0)

step("Run the SMF fixture and require the compiled wrapper path")
val (run_out, run_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(run_code).to_equal(0)
expect(run_out).to_contain("multicore_green_parallelism")
expect(run_out).to_contain("got = 42")
expect(run_out).to_contain("wrapper_smf_pool_pass=true")

step("Verify the blocker document records the resolved failure")
val blocker = read_text("doc/08_tracking/bug/smf_runtime_pool_closure_lookup_2026-06-07.md")
expect(blocker).to_contain("**Status:** Closed")
expect(blocker).to_contain("function not found: spawn_worker")
expect(blocker).to_contain("spawn_worker()")
expect(blocker).to_contain("wrapper_smf_pool_pass=true")
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

- Canonical SPipe generation for source `c54c0b288e60ef25e7e5bf754bb4da1aabadf935bba8a221b5f9d38dfed1c5ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c54c0b288e60ef25e7e5bf754bb4da1aabadf935bba8a221b5f9d38dfed1c5ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c54c0b288e60ef25e7e5bf754bb4da1aabadf935bba8a221b5f9d38dfed1c5ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the wrapper-shaped multicore-green SMF path executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
