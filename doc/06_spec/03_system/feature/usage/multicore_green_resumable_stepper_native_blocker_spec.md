# Multicore Green Resumable Stepper Native Blocker

> This SSpec keeps the historical host-native blocker closed for the best explicit fairness path found so far: a resumable stepper scheduler over the existing `multicore_green` worker pool. The generated probe type-checks, compiles to a native binary, and returns the first completion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Resumable Stepper Native Blocker

This SSpec keeps the historical host-native blocker closed for the best explicit fairness path found so far: a resumable stepper scheduler over the existing `multicore_green` worker pool. The generated probe type-checks, compiles to a native binary, and returns the first completion.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-resumable-stepper-native-blocker |
| Category | Runtime / Native / Concurrency |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the historical host-native blocker closed for the best
explicit fairness path found so far: a resumable stepper scheduler over the
existing `multicore_green` worker pool. The generated probe type-checks,
compiles to a native binary, and returns the first completion.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md

## Syntax

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl
multicore green resumable stepper native blocker PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The generated probe models a resumable stepper over multicore-green workers.
- The probe uses callback ids rather than sharing mutable closures across tasks.
- The generated source must type-check before native compilation.
- The standalone native compile must succeed before run evidence is accepted.
- The run output must include the expected first-completion result.
- The tracker must keep the historical blocker marked closed.
- The test command must honor `SIMPLE_BIN` for Docker-isolated runs.
- The Syntax block must not point at the stale `bin/release/simple` wrapper.
- This spec is perf-sensitive because it compiles a generated native probe.
- Short verification may use `simple check` when the full native run is too slow.
- The supported public fairness API remains `multicore_green_spawn_sliced`.
- Ordinary `multicore_green_spawn` closure preemption remains future work.

## Scenarios

### multicore green resumable stepper native regression

#### keeps the historical native crash boundary closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the historical native crash boundary closed
- Write the resumable-stepper probe source
   - Expected: write_code equals `0`
- The generated probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile succeeds for the resumable-stepper path
   - Expected: compile_code equals `0`
- The native probe returns the completed stepper value
   - Expected: native_code equals `0`
- The tracker records the stepper path as closed
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the historical native crash boundary closed")
step("Write the resumable-stepper probe source")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The generated probe still type-checks under the fresh debug compiler")
val (check_out, check_code) = shell(simple_bin() + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Hosted native compile succeeds for the resumable-stepper path")
val (compile_out, compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe returns the completed stepper value")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/mcg_resumable_stepper.out 2>&1; code=$?; cat /tmp/mcg_resumable_stepper.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("result=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the stepper path as closed")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: closed")
expect(blocker).to_contain("resumable stepper native path returns")
expect(blocker).to_contain("EXIT=0")
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
- **Research:** `doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c4da2b3cd3fbc63ae53cdc18e86965f04e3c38d245fe3d06838e8f4e4b12d34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c4da2b3cd3fbc63ae53cdc18e86965f04e3c38d245fe3d06838e8f4e4b12d34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c4da2b3cd3fbc63ae53cdc18e86965f04e3c38d245fe3d06838e8f4e4b12d34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_resumable_stepper_native_blocker_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the historical native crash boundary closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
