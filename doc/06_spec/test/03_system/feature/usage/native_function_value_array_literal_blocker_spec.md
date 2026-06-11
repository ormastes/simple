# Native Function Value Array Literal Blocker

> This SSpec pins the current lower native blocker beneath the hosted `multicore_green` resumable-stepper lane. A plain array literal containing function values already crashes on current-source native, so the worker-pool stepper lane cannot be closed above it yet.

<!-- sdn-diagram:id=native_function_value_array_literal_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_function_value_array_literal_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_function_value_array_literal_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_function_value_array_literal_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Array Literal Blocker

This SSpec pins the current lower native blocker beneath the hosted `multicore_green` resumable-stepper lane. A plain array literal containing function values already crashes on current-source native, so the worker-pool stepper lane cannot be closed above it yet.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-array-literal-blocker |
| Category | Runtime / Native / Function Values |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_array_literal_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current lower native blocker beneath the hosted
`multicore_green` resumable-stepper lane. A plain array literal containing
function values already crashes on current-source native, so the worker-pool
stepper lane cannot be closed above it yet.

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
bin/release/simple test test/03_system/feature/usage/native_function_value_array_literal_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value array literal blocker

#### keeps the lower hosted-native array-literal crash explicit

- Write the function-value array-literal probe
   - Expected: write_code equals `0`
- Hosted native compile still succeeds before the crash boundary
   - Expected: compile_code equals `0`
- The native probe still crashes when calling through the array literal
   - Expected: native_code equals `0`
- The tracker records the same narrowed blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the function-value array-literal probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("Hosted native compile still succeeds before the crash boundary")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe still crashes when calling through the array literal")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_fn_array_literal.out 2>&1; code=$?; cat /tmp/native_fn_array_literal.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("before")
expect(native_out).to_contain("EXIT=139")

step("The tracker records the same narrowed blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: open")
expect(blocker).to_contain("array literal containing function values")
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
- **Research:** [doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md](doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md)


</details>
