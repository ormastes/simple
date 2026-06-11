# Native Function Value Helper Return Debug Blocker

> This SSpec pins the current narrower debug-seed callback boundary under the hosted multicore-green resumable-stepper experiment: the checked-in `bin/release/simple` path now handles helper-returned function values, but the fresh debug seed binary still segfaults when a helper returns a function value and the caller invokes it in the standalone native artifact.

<!-- sdn-diagram:id=native_function_value_helper_return_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_function_value_helper_return_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_function_value_helper_return_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_function_value_helper_return_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Helper Return Debug Blocker

This SSpec pins the current narrower debug-seed callback boundary under the hosted multicore-green resumable-stepper experiment: the checked-in `bin/release/simple` path now handles helper-returned function values, but the fresh debug seed binary still segfaults when a helper returns a function value and the caller invokes it in the standalone native artifact.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-helper-return |
| Category | Runtime / Native / Function Values |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_helper_return_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current narrower debug-seed callback boundary under the
hosted multicore-green resumable-stepper experiment: the checked-in
`bin/release/simple` path now handles helper-returned function values, but the
fresh debug seed binary still segfaults when a helper returns a function value
and the caller invokes it in the standalone native artifact.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md

## Syntax

```sh
bin/release/simple test test/03_system/feature/usage/native_function_value_helper_return_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value helper return blocker

#### keeps the remaining debug-seed helper-return crash boundary explicit

- Write the direct and helper-return native callback probes
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(DIRECT_SOURCE, direct_probe_source()) is true
   - Expected: rt_file_write_text(HELPER_SOURCE, helper_probe_source()) is true
- Direct global-array callback still works in the fresh debug native path
   - Expected: direct_compile_code equals `0`
   - Expected: direct_run_code equals `0`
- The checked-in release path now handles helper-returned function values
   - Expected: release_compile_code equals `0`
   - Expected: release_run_code equals `0`
- The fresh debug seed binary still crashes on the helper-return native path
   - Expected: helper_compile_code equals `0`
   - Expected: helper_run_code equals `0`
- The tracker records the same debug-seed helper-return blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the direct and helper-return native callback probes")
val (_mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(DIRECT_SOURCE, direct_probe_source())).to_equal(true)
expect(rt_file_write_text(HELPER_SOURCE, helper_probe_source())).to_equal(true)

step("Direct global-array callback still works in the fresh debug native path")
val (direct_compile_out, direct_compile_code) = shell(DEBUG_SIMPLE_BIN + " compile " + DIRECT_SOURCE + " --native -o " + DIRECT_NATIVE_DEBUG)
expect(direct_compile_code).to_equal(0)
expect(direct_compile_out).to_contain("Compiled")
val (direct_run_out, direct_run_code) = shell("sh -c '" + DIRECT_NATIVE_DEBUG + " >/tmp/native_fn_direct.out 2>&1; code=$?; cat /tmp/native_fn_direct.out; echo EXIT=$code'")
expect(direct_run_code).to_equal(0)
expect(direct_run_out).to_contain("got=<value:0x7>")
expect(direct_run_out).to_contain("EXIT=0")

step("The checked-in release path now handles helper-returned function values")
val (release_compile_out, release_compile_code) = shell(RELEASE_SIMPLE_BIN + " compile " + HELPER_SOURCE + " --native -o " + HELPER_NATIVE_RELEASE)
expect(release_compile_code).to_equal(0)
expect(release_compile_out).to_contain("Compiled")
val (release_run_out, release_run_code) = shell("sh -c '" + HELPER_NATIVE_RELEASE + " >/tmp/native_fn_helper_release.out 2>&1; code=$?; cat /tmp/native_fn_helper_release.out; echo EXIT=$code'")
expect(release_run_code).to_equal(0)
expect(release_run_out).to_contain("via_helper=7")
expect(release_run_out).to_contain("EXIT=0")

step("The fresh debug seed binary still crashes on the helper-return native path")
val (helper_compile_out, helper_compile_code) = shell(DEBUG_SIMPLE_BIN + " compile " + HELPER_SOURCE + " --native -o " + HELPER_NATIVE_DEBUG)
expect(helper_compile_code).to_equal(0)
expect(helper_compile_out).to_contain("Compiled")
val (helper_run_out, helper_run_code) = shell("sh -c '" + HELPER_NATIVE_DEBUG + " >/tmp/native_fn_helper.out 2>&1; code=$?; cat /tmp/native_fn_helper.out; echo EXIT=$code'")
expect(helper_run_code).to_equal(0)
expect(helper_run_out).to_contain("EXIT=139")

step("The tracker records the same debug-seed helper-return blocker")
val (blocker_out, blocker_code) = shell("cat doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker_out).to_contain("Status: open")
expect(blocker_out).to_contain("checked-in release path now handles helper-returned function values")
expect(blocker_out).to_contain("fresh debug seed binary still segfaults")
expect(blocker_out).to_contain("EXIT=139")
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
- **Research:** [doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md](doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md)


</details>
