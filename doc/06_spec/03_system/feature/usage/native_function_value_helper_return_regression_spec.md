# Native Function Value Helper Return Regression

> This SSpec keeps native helper-returned function values covered after the hybrid-compilability and HIR function-value typing fixes. Both scalar and object-returning function arrays must preserve the returned callable and invoke it correctly in fresh native artifacts.

<!-- sdn-diagram:id=native_function_value_helper_return_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_function_value_helper_return_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_function_value_helper_return_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_function_value_helper_return_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Helper Return Regression

This SSpec keeps native helper-returned function values covered after the hybrid-compilability and HIR function-value typing fixes. Both scalar and object-returning function arrays must preserve the returned callable and invoke it correctly in fresh native artifacts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-helper-return-regression |
| Category | Runtime / Native / Function Values |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps native helper-returned function values covered after the
hybrid-compilability and HIR function-value typing fixes. Both scalar and
object-returning function arrays must preserve the returned callable and invoke
it correctly in fresh native artifacts.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value helper return regression

#### keeps scalar and object-returning helper values native and callable

- Write the scalar and object-return helper probes
- " && cat > " + SCALAR SOURCE + " <<'EOF1'\n" + scalar probe
- "cat > " + STRUCT SOURCE + " <<'EOF2'\n" + struct probe
   - Expected: write_code equals `0`
- Compile both probes to standalone native binaries
   - Expected: scalar_compile_code equals `0`
   - Expected: struct_compile_code equals `0`
- The scalar helper-return probe now preserves and invokes the returned function value
   - Expected: scalar_run_code equals `0`
- The object-return helper-return probe also preserves and invokes the returned function value
   - Expected: struct_run_code equals `0`
- The blocker tracker records this boundary as closed
   - Expected: tracker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the scalar and object-return helper probes")
val (write_out, write_code) = shell(
    "mkdir -p " + BUILD_DIR +
    " && cat > " + SCALAR_SOURCE + " <<'EOF1'\n" + scalar_probe() + "\nEOF1\n" +
    "cat > " + STRUCT_SOURCE + " <<'EOF2'\n" + struct_probe() + "\nEOF2"
)
expect(write_out.len()).to_be_greater_than(-1)
expect(write_code).to_equal(0)

step("Compile both probes to standalone native binaries")
val (scalar_compile_out, scalar_compile_code) = shell(SIMPLE_BIN + " compile " + SCALAR_SOURCE + " --native -o " + SCALAR_NATIVE)
expect(scalar_compile_code).to_equal(0)
expect(scalar_compile_out).to_contain("Compiled")
val (struct_compile_out, struct_compile_code) = shell(SIMPLE_BIN + " compile " + STRUCT_SOURCE + " --native -o " + STRUCT_NATIVE)
expect(struct_compile_code).to_equal(0)
expect(struct_compile_out).to_contain("Compiled")

step("The scalar helper-return probe now preserves and invokes the returned function value")
val (scalar_run_out, scalar_run_code) = shell(SCALAR_NATIVE)
expect(scalar_run_out).to_contain("got=7")
expect(scalar_run_code).to_equal(0)

step("The object-return helper-return probe also preserves and invokes the returned function value")
val (struct_run_out, struct_run_code) = shell(STRUCT_NATIVE)
expect(struct_run_out).to_contain("done=true")
expect(struct_run_out).to_contain("value=7")
expect(struct_run_code).to_equal(0)

step("The blocker tracker records this boundary as closed")
val (tracker_out, tracker_code) = shell("cat doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_contain("Status: closed")
expect(tracker_out).to_contain("scalar and object-returning helper probes")
expect(tracker_out).to_contain("resumable-stepper native crash remains a separate blocker")
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
