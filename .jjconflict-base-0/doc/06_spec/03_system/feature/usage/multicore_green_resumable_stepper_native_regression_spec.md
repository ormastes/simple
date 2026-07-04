# Multicore Green Resumable Stepper Native Regression

> This SSpec keeps the best explicit host-fairness path green: a resumable stepper scheduler over the existing `multicore_green` worker pool. The probe uses callback ids, channels, a bounded runtime-pool worker, a handle array, and an ordered result array, then returns the completed value from standalone native.

<!-- sdn-diagram:id=multicore_green_resumable_stepper_native_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_resumable_stepper_native_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_resumable_stepper_native_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_resumable_stepper_native_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Resumable Stepper Native Regression

This SSpec keeps the best explicit host-fairness path green: a resumable stepper scheduler over the existing `multicore_green` worker pool. The probe uses callback ids, channels, a bounded runtime-pool worker, a handle array, and an ordered result array, then returns the completed value from standalone native.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-resumable-stepper-native-regression |
| Category | Runtime / Native / Concurrency |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_resumable_stepper_native_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the best explicit host-fairness path green: a resumable
stepper scheduler over the existing `multicore_green` worker pool. The probe
uses callback ids, channels, a bounded runtime-pool worker, a handle array, and
an ordered result array, then returns the completed value from standalone
native.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_resumable_stepper_native_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green resumable stepper native regression

#### keeps the current native resumable-stepper path green

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
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Hosted native compile succeeds for the resumable-stepper path")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
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
