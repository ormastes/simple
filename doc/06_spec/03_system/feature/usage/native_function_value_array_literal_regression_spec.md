# Native Function Value Array Literal Regression

> This SSpec keeps the fixed lower native path green beneath the hosted `multicore_green` resumable-stepper lane. A plain array literal containing an inline lambda must preserve the function element type, keep the closure unboxed in the array, and call through the array slot with the lambda body return type.

<!-- sdn-diagram:id=native_function_value_array_literal_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_function_value_array_literal_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_function_value_array_literal_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_function_value_array_literal_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Array Literal Regression

This SSpec keeps the fixed lower native path green beneath the hosted `multicore_green` resumable-stepper lane. A plain array literal containing an inline lambda must preserve the function element type, keep the closure unboxed in the array, and call through the array slot with the lambda body return type.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-array-literal-regression |
| Category | Runtime / Native / Function Values |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the fixed lower native path green beneath the hosted
`multicore_green` resumable-stepper lane. A plain array literal containing
an inline lambda must preserve the function element type, keep the closure
unboxed in the array, and call through the array slot with the lambda body
return type.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value array literal regression

#### keeps inline lambda array literal native calls green

- Write the function-value array-literal probe
   - Expected: write_code equals `0`
- Hosted native compile succeeds on the fixed lower path
   - Expected: compile_code equals `0`
- The native probe calls through the array literal and returns the lambda value
   - Expected: native_code equals `0`
- The tracker records the closed lower blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the function-value array-literal probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("Hosted native compile succeeds on the fixed lower path")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe calls through the array literal and returns the lambda value")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_fn_array_literal.out 2>&1; code=$?; cat /tmp/native_fn_array_literal.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("before")
expect(native_out).to_contain("value=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the closed lower blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: closed")
expect(blocker).to_contain("array literal containing function values")
expect(blocker).to_contain("value=7")
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
- **Research:** [doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md](doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md)


</details>
