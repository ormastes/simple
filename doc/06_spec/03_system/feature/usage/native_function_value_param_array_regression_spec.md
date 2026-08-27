# Native Function Value Param Array Regression

> This SSpec covers the closed lower native blocker beneath the hosted `multicore_green` resumable-stepper lane. A function-valued parameter or local stored into an array now stays green on current-source native.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Param Array Regression

This SSpec covers the closed lower native blocker beneath the hosted `multicore_green` resumable-stepper lane. A function-valued parameter or local stored into an array now stays green on current-source native.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-param-array-regression |
| Category | Runtime / Native / Function Values |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec covers the closed lower native blocker beneath the hosted
`multicore_green` resumable-stepper lane. A function-valued parameter or local
stored into an array now stays green on current-source native.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value param array regression

#### keeps the fixed local or param array path green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the fixed local or param array path green
- Write the function-valued param array probe
   - Expected: write_out equals ``
   - Expected: write_code equals `0`
- The probe still runs in source mode
   - Expected: run_code equals `0`
- Hosted native compile succeeds on the fixed lower path
   - Expected: compile_code equals `0`
- The standalone native probe now stays green on the local or param array path
   - Expected: native_code equals `0`
- The tracker records the lower blocker as closed
   - Expected: tracker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the fixed local or param array path green")
step("Write the function-valued param array probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out).to_equal("")
expect(write_code).to_equal(0)

step("The probe still runs in source mode")
val (run_out, run_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(run_code).to_equal(0)
expect(run_out).to_contain("before")
expect(run_out).to_contain("after=7")

step("Hosted native compile succeeds on the fixed lower path")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The standalone native probe now stays green on the local or param array path")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_fn_param_array.out 2>&1; code=$?; cat /tmp/native_fn_param_array.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("before")
expect(native_out).to_contain("after=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the lower blocker as closed")
val (tracker_out, tracker_code) = shell("cat doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_contain("Status: closed")
expect(tracker_out).to_contain("stored into an array")
expect(tracker_out).to_contain("after=7")
expect(tracker_out).to_contain("EXIT=0")
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
- **Research:** `doc/08_tracking/bug/native_function_value_param_array_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91d0cbc7f6cd7fcc1a58cc7d5636dd57acad4f81dc29231b1013f67c724da437`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91d0cbc7f6cd7fcc1a58cc7d5636dd57acad4f81dc29231b1013f67c724da437`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91d0cbc7f6cd7fcc1a58cc7d5636dd57acad4f81dc29231b1013f67c724da437`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/native_function_value_param_array_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/native_function_value_param_array_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/native_function_value_param_array_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/native_function_value_param_array_regression_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the fixed local or param array path green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
