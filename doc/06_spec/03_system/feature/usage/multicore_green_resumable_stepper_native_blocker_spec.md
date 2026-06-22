# Multicore Green Resumable Stepper Native Blocker

> This SSpec keeps the historical host-native blocker closed for the best explicit fairness path found so far: a resumable stepper scheduler over the existing `multicore_green` worker pool. The generated probe type-checks, compiles to a native binary, and returns the first completion.

<!-- sdn-diagram:id=multicore_green_resumable_stepper_native_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_resumable_stepper_native_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_resumable_stepper_native_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_resumable_stepper_native_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
Simple Test Runner v1.0.0-beta
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

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md](doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md)


</details>
