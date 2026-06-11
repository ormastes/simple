# Multicore Green Callable Field Runtime Regression

> This SSpec covers the fixed callable-field runtime boundary underneath the broader multicore-green sliced fairness experiment: a zero-argument function-valued object field backed by captured mutable state now works on both source-run and standalone native.

<!-- sdn-diagram:id=multicore_green_callable_field_runtime_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_callable_field_runtime_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_callable_field_runtime_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_callable_field_runtime_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Callable Field Runtime Regression

This SSpec covers the fixed callable-field runtime boundary underneath the broader multicore-green sliced fairness experiment: a zero-argument function-valued object field backed by captured mutable state now works on both source-run and standalone native.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-callable-field-runtime |
| Category | Runtime / Native / Concurrency |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec covers the fixed callable-field runtime boundary underneath the
broader multicore-green sliced fairness experiment: a zero-argument
function-valued object field backed by captured mutable state now works on both
source-run and standalone native.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the regression contract:

```sh
bin/release/simple test test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### Multicore green callable field runtime regression

#### keeps the escaped callable-field closure path working

- Write the hosted callable-field probe
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Source-run keeps the expected captured-thunk values
   - Expected: run_code equals `0`
- Standalone native keeps the same escaped captured-callable shape working
   - Expected: compile_code equals `0`
   - Expected: native_code equals `0`
- The tracking note records the fixed callable-field boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the hosted callable-field probe")
val (_mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, fixture_source())).to_equal(true)

step("Source-run keeps the expected captured-thunk values")
val (run_out, run_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(run_code).to_equal(0)
expect(run_out).to_contain("a=41")
expect(run_out).to_contain("b=42")

step("Standalone native keeps the same escaped captured-callable shape working")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/mcg_callable_field.out 2>&1; code=$?; cat /tmp/mcg_callable_field.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("a=41")
expect(native_out).to_contain("b=42")
expect(native_out).to_contain("EXIT=0")

step("The tracking note records the fixed callable-field boundary")
val blocker = read_text("doc/08_tracking/bug/multicore_green_callable_field_runtime_blocker_2026-06-11.md")
expect(blocker).to_contain("Status: fixed")
expect(blocker).to_contain("fresh native compiler/runtime now runs the same probe successfully")
expect(blocker).to_contain("a=41")
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
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
