# Multicore Green Post-Join Array Return Native Blocker

> This SSpec pins the narrower native blocker found after the resumable-stepper path itself became green. A `run_steppers` function that joins a `multicore_green` worker and then performs extra post-join string work before returning a local result array still segfaults in standalone native.

<!-- sdn-diagram:id=multicore_green_post_join_array_return_native_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_post_join_array_return_native_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_post_join_array_return_native_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_post_join_array_return_native_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Post-Join Array Return Native Blocker

This SSpec pins the narrower native blocker found after the resumable-stepper path itself became green. A `run_steppers` function that joins a `multicore_green` worker and then performs extra post-join string work before returning a local result array still segfaults in standalone native.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-post-join-array-return-native-blocker |
| Category | Runtime / Native / Concurrency |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md |
| Source | `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the narrower native blocker found after the resumable-stepper
path itself became green. A `run_steppers` function that joins a
`multicore_green` worker and then performs extra post-join string work before
returning a local result array still segfaults in standalone native.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green post join array return native blocker

#### keeps the narrowed post-join native crash explicit

- Write the post-join array-return probe source
   - Expected: write_code equals `0`
- The generated probe still type-checks
   - Expected: check_code equals `0`
- Hosted native compile succeeds before the narrowed runtime crash
   - Expected: compile_code equals `0`
- The native probe still crashes after joining before returning the array
   - Expected: native_code equals `0`
- The tracker records the narrowed blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the post-join array-return probe source")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The generated probe still type-checks")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Hosted native compile succeeds before the narrowed runtime crash")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe still crashes after joining before returning the array")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/mcg_post_join_array_return.out 2>&1; code=$?; cat /tmp/mcg_post_join_array_return.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("EXIT=139")

step("The tracker records the narrowed blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: open")
expect(blocker).to_contain("post-join")
expect(blocker).to_contain("EXIT=139")
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
- **Research:** [doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md](doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md)


</details>
