# Cooperative Green SMF Function-Global Regression

> This SSpec keeps SMF function-valued global storage covered after the runtime fix that restored `__module_init` execution before SMF entry calls. Minimal SMF fixtures with a function-valued global slot or a global function-valued array must both compile and run successfully.

<!-- sdn-diagram:id=cooperative_green_smf_function_global_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cooperative_green_smf_function_global_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cooperative_green_smf_function_global_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cooperative_green_smf_function_global_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green SMF Function-Global Regression

This SSpec keeps SMF function-valued global storage covered after the runtime fix that restored `__module_init` execution before SMF entry calls. Minimal SMF fixtures with a function-valued global slot or a global function-valued array must both compile and run successfully.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-smf-function-global |
| Category | Runtime / SMF / Concurrency |
| Status | Regression Coverage |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps SMF function-valued global storage covered after the runtime
fix that restored `__module_init` execution before SMF entry calls. Minimal SMF
fixtures with a function-valued global slot or a global function-valued array
must both compile and run successfully.

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
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl --mode=interpreter --clean
```

## Examples

- The function-valued global-slot fixture must compile to SMF and print its pass marker.
- The global function-array fixture must compile to SMF and print its pass marker.
- The regression closes the historical crash path where SMF skipped `__module_init`
  before entering `spl_main`.

## Scenarios

### Cooperative green SMF function-global regression

#### runs SMF function-valued globals and global arrays after module init

- Write the minimal function-valued SMF fixtures
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(FUNCTION_GLOBAL_SOURCE, function_global_fixture_source()) is true
   - Expected: rt_file_write_text(GLOBAL_ARRAY_SOURCE, global_function_array_fixture_source()) is true
- Compile the function-valued global-slot fixture to SMF
   - Expected: compile_global_code equals `0`
- Compile the global function-array fixture to SMF
   - Expected: compile_array_code equals `0`
- Run the function-valued global-slot SMF and verify the pass marker
   - Expected: run_global_code equals `0`
- Run the global function-array SMF and verify the pass marker
   - Expected: run_array_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the minimal function-valued SMF fixtures")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(FUNCTION_GLOBAL_SOURCE, function_global_fixture_source())).to_equal(true)
expect(rt_file_write_text(GLOBAL_ARRAY_SOURCE, global_function_array_fixture_source())).to_equal(true)

step("Compile the function-valued global-slot fixture to SMF")
val (compile_global_out, compile_global_code) = shell(SIMPLE_BIN + " compile " + FUNCTION_GLOBAL_SOURCE + " -o " + FUNCTION_GLOBAL_SMF)
expect(compile_global_out).to_contain("Compiled")
expect(compile_global_code).to_equal(0)

step("Compile the global function-array fixture to SMF")
val (compile_array_out, compile_array_code) = shell(SIMPLE_BIN + " compile " + GLOBAL_ARRAY_SOURCE + " -o " + GLOBAL_ARRAY_SMF)
expect(compile_array_out).to_contain("Compiled")
expect(compile_array_code).to_equal(0)

step("Run the function-valued global-slot SMF and verify the pass marker")
val (run_global_out, run_global_code) = shell("timeout 20s " + SIMPLE_BIN + " " + FUNCTION_GLOBAL_SMF)
expect(run_global_out).to_contain("function_global_smf_pass=true")
expect(run_global_code).to_equal(0)

step("Run the global function-array SMF and verify the pass marker")
val (run_array_out, run_array_code) = shell("timeout 20s " + SIMPLE_BIN + " " + GLOBAL_ARRAY_SMF)
expect(run_array_out).to_contain("global_function_array_smf_pass=true")
expect(run_array_code).to_equal(0)
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
