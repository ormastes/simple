# Multicore Green Handle Array Join Native Regression

> This SSpec regression-covers the hosted-native helper path where an inferred empty local handle array is populated with `append`, iterated, and joined.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Handle Array Join Native Regression

This SSpec regression-covers the hosted-native helper path where an inferred empty local handle array is populated with `append`, iterated, and joined.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-handle-array-join-native-blocker |
| Category | Runtime / Native / Concurrency |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec regression-covers the hosted-native helper path where an inferred
empty local handle array is populated with `append`, iterated, and joined.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md

## Syntax

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl
multicore green handle-array join native regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The probe imports `multicore_green_spawn` from the multicore-green facade.
- The probe uses a local inferred handle array.
- The probe appends a `MulticoreGreenHandle` returned by `multicore_green_spawn`.
- The probe iterates the handle array and calls `join()`.
- The generated native binary must print `result=7`.
- The generated native binary must exit with `EXIT=0`.
- The tracker must keep the lower handle-array blocker marked closed.
- The test command must honor `SIMPLE_BIN` for Docker-isolated runs.
- The Syntax block must not point at the stale `bin/release/simple` wrapper.
- This regression protects runtime-pool host evidence under the M:N lane.
- It does not claim ordinary-closure preemption or sliced fairness.
- The generated manual must keep the native compile/run boundary visible.

## Scenarios

### multicore green handle-array join native regression

#### keeps local handle-array iteration and join native

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps local handle-array iteration and join native
- Write the reduced handle-array join probe
   - Expected: write_code equals `0`
- The reduced probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile succeeds for the helper loop
   - Expected: compile_code equals `0`
- The native probe joins the indexed handles and returns the worker result
   - Expected: native_code equals `0`
- The tracker records the closed lower blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps local handle-array iteration and join native")
step("Write the reduced handle-array join probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out.len()).to_be_greater_than(-1)
expect(write_code).to_equal(0)

step("The reduced probe still type-checks under the fresh debug compiler")
val (_, check_code) = shell(simple_bin() + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)

step("Hosted native compile succeeds for the helper loop")
val (_, compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)

step("The native probe joins the indexed handles and returns the worker result")
val (native_out, native_code) = shell("sh -c './" + NATIVE_PATH + " >/tmp/mcg_handle_array_join_probe.out 2>&1; code=$?; cat /tmp/mcg_handle_array_join_probe.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("result=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the closed lower blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: closed")
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
- **Research:** `doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `adadf02f28a4d66f63c7b54335064c4dddcd0e1ca61bfac46ddfac54a869f616`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `adadf02f28a4d66f63c7b54335064c4dddcd0e1ca61bfac46ddfac54a869f616`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `adadf02f28a4d66f63c7b54335064c4dddcd0e1ca61bfac46ddfac54a869f616`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps local handle-array iteration and join native' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
