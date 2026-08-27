# Native Function Value Loop Return Regression

> This SSpec regression-covers the lower native helper path that previously sat beneath the hosted `multicore_green` resumable-stepper experiment: returning a function value from inside a loop/search branch now works in standalone native artifacts for a plain named `fn() -> i64`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Loop Return Regression

This SSpec regression-covers the lower native helper path that previously sat beneath the hosted `multicore_green` resumable-stepper experiment: returning a function value from inside a loop/search branch now works in standalone native artifacts for a plain named `fn() -> i64`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-loop-return-regression |
| Category | Runtime / Native / Function Values |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec regression-covers the lower native helper path that previously sat
beneath the hosted `multicore_green` resumable-stepper experiment: returning a
function value from inside a loop/search branch now works in standalone native
artifacts for a plain named `fn() -> i64`.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value loop return regression

<details>
<summary>Advanced: keeps the standalone native loop-return helper green</summary>

#### keeps the standalone native loop-return helper green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the standalone native loop-return helper green
- Write the loop-return function-value probe
   - Expected: write_out equals ``
   - Expected: write_code equals `0`
- The probe still runs in source mode
   - Expected: run_code equals `0`
   - Expected: run_out equals ``
- Hosted native compile still succeeds
   - Expected: compile_code equals `0`
- The standalone native probe now returns cleanly on the loop-return path
   - Expected: native_code equals `0`
- The tracker records the blocker as closed and points higher fairness work at the remaining stepper crash
   - Expected: tracker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the standalone native loop-return helper green")
step("Write the loop-return function-value probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out).to_equal("")
expect(write_code).to_equal(0)

step("The probe still runs in source mode")
val (run_out, run_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(run_code).to_equal(0)
expect(run_out).to_equal("")

step("Hosted native compile still succeeds")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The standalone native probe now returns cleanly on the loop-return path")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_loop_return.out 2>&1; code=$?; cat /tmp/native_loop_return.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("EXIT=0")

step("The tracker records the blocker as closed and points higher fairness work at the remaining stepper crash")
val (tracker_out, tracker_code) = shell("cat doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_contain("Status: closed")
expect(tracker_out).to_contain("source-run: passes")
expect(tracker_out).to_contain("native run: EXIT=0")
expect(tracker_out).to_contain("resumable-stepper")
```

</details>


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
- **Research:** `doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab23991c3eaf1573cd32b99ef301b8f519eb5956253d1634d3d99dc6789ea685`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab23991c3eaf1573cd32b99ef301b8f519eb5956253d1634d3d99dc6789ea685`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab23991c3eaf1573cd32b99ef301b8f519eb5956253d1634d3d99dc6789ea685`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/native_function_value_loop_return_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/native_function_value_loop_return_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/native_function_value_loop_return_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the standalone native loop-return helper green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
