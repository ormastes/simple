# Native Function Value Loop Return Blocker

> This SSpec pins the current lower native blocker beneath the hosted `multicore_green` resumable-stepper experiment: returning a function value from inside a loop/search branch still crashes in standalone native artifacts, even for a plain named `fn() -> i64`.

<!-- sdn-diagram:id=native_function_value_loop_return_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_function_value_loop_return_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_function_value_loop_return_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_function_value_loop_return_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Loop Return Blocker

This SSpec pins the current lower native blocker beneath the hosted `multicore_green` resumable-stepper experiment: returning a function value from inside a loop/search branch still crashes in standalone native artifacts, even for a plain named `fn() -> i64`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-loop-return-blocker |
| Category | Runtime / Native / Function Values |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_loop_return_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current lower native blocker beneath the hosted
`multicore_green` resumable-stepper experiment: returning a function value from
inside a loop/search branch still crashes in standalone native artifacts, even
for a plain named `fn() -> i64`.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_loop_return_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value loop return blocker

<details>
<summary>Advanced: keeps the current standalone native loop-return crash explicit</summary>

#### keeps the current standalone native loop-return crash explicit

- Write the loop-return function-value probe
   - Expected: write_out equals ``
   - Expected: write_code equals `0`
- The probe still runs in source mode
   - Expected: run_code equals `0`
   - Expected: run_out equals ``
- Hosted native compile still succeeds before the runtime crash boundary
   - Expected: compile_code equals `0`
- The standalone native probe still crashes on the loop-return path
   - Expected: native_code equals `0`
- The blocker tracker records the same lower native boundary
   - Expected: tracker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the loop-return function-value probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out).to_equal("")
expect(write_code).to_equal(0)

step("The probe still runs in source mode")
val (run_out, run_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(run_code).to_equal(0)
expect(run_out).to_equal("")

step("Hosted native compile still succeeds before the runtime crash boundary")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The standalone native probe still crashes on the loop-return path")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_loop_return.out 2>&1; code=$?; cat /tmp/native_loop_return.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("EXIT=139")

step("The blocker tracker records the same lower native boundary")
val (tracker_out, tracker_code) = shell("cat doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_contain("Status: open")
expect(tracker_out).to_contain("loop/search branch still crashes")
expect(tracker_out).to_contain("return/control-flow correctness")
expect(tracker_out).to_contain("EXIT=139")
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

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md](doc/08_tracking/bug/native_function_value_loop_return_blocker_2026-06-11.md)


</details>
