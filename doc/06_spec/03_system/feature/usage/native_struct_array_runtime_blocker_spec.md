# Native Struct Array Runtime Regression

> This SSpec keeps the closed lower hosted-native struct-array regression covered. A direct native array of by-value structs is green again on current-source seed/native and should stay that way while the higher `multicore_green` handle-array blocker is fixed.

<!-- sdn-diagram:id=native_struct_array_runtime_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_struct_array_runtime_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_struct_array_runtime_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_struct_array_runtime_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Struct Array Runtime Regression

This SSpec keeps the closed lower hosted-native struct-array regression covered. A direct native array of by-value structs is green again on current-source seed/native and should stay that way while the higher `multicore_green` handle-array blocker is fixed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-struct-array-runtime-blocker |
| Category | Runtime / Native / Collections |
| Status | Regression Covered |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the closed lower hosted-native struct-array regression
covered. A direct native array of by-value structs is green again on
current-source seed/native and should stay that way while the higher
`multicore_green` handle-array blocker is fixed.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md

## Syntax

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl
native struct array runtime regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The fixture writes a direct array of by-value `Boxed` structs.
- The same generated source is checked and compiled by `SIMPLE_BIN`.
- The standalone native output must contain `result=7`.
- The standalone native exit marker must contain `EXIT=0`.
- The test command must honor `SIMPLE_BIN` for Docker-isolated runs.
- The Syntax block must not point at the stale `bin/release/simple` wrapper.
- The closed native struct-array tracker must remain linked.

## Scenarios

### native struct array runtime regression

#### keeps the closed native struct-array path green

- Write the direct struct-array probe source
   - Expected: write_code equals `0`
- The generated probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile still succeeds
   - Expected: compile_code equals `0`
- The native probe now returns the expected result boundary
   - Expected: native_code equals `0`
- The tracker records the lower blocker as closed
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the direct struct-array probe source")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The generated probe still type-checks under the fresh debug compiler")
val (_, check_code) = shell(simple_bin() + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)

step("Hosted native compile still succeeds")
val (_, compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)

step("The native probe now returns the expected result boundary")
val (native_out, native_code) = shell("sh -c './" + NATIVE_PATH + " >/tmp/native_struct_array_probe.out 2>&1; code=$?; cat /tmp/native_struct_array_probe.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("result=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the lower blocker as closed")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md")
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

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md](doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md)


</details>
