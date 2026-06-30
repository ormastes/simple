# Multicore Green Explicit Sliced Fairness Regression

> This SSpec proves the explicit Pure Simple sliced-task API can provide a hosted fairness contract without claiming automatic preemption for ordinary `multicore_green_spawn` closures. With hosted parallelism pinned to `1`, a long sliced task requeues itself between short slices, allowing a later quick task to complete during the first observation window on both source-run and standalone native paths.

<!-- sdn-diagram:id=multicore_green_sliced_fairness_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_sliced_fairness_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_sliced_fairness_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_sliced_fairness_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Explicit Sliced Fairness Regression

This SSpec proves the explicit Pure Simple sliced-task API can provide a hosted fairness contract without claiming automatic preemption for ordinary `multicore_green_spawn` closures. With hosted parallelism pinned to `1`, a long sliced task requeues itself between short slices, allowing a later quick task to complete during the first observation window on both source-run and standalone native paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-sliced-fairness |
| Category | Runtime / Hosted / Multicore Green |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec proves the explicit Pure Simple sliced-task API can provide a
hosted fairness contract without claiming automatic preemption for ordinary
`multicore_green_spawn` closures. With hosted parallelism pinned to `1`, a
long sliced task requeues itself between short slices, allowing a later quick
task to complete during the first observation window on both source-run and
standalone native paths.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green explicit sliced fairness

#### lets a quick task run between explicit slices without growing hosted parallelism

- Prepare the native output directory for the sliced fairness fixture
   - Expected: mkdir_code equals `0`
- The fixture type-checks with the public sliced API
   - Expected: check_code equals `0`
- Compile the fixture to standalone native
   - Expected: native_compile_code equals `0`
- Run the fixture through the hosted source path
- expect sliced fairness output
   - Expected: interp_code equals `0`
- Run the fixture through the hosted standalone native path
- expect sliced fairness output
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare the native output directory for the sliced fairness fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)

step("The fixture type-checks with the public sliced API")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture through the hosted source path")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect_sliced_fairness_output(interp_out)
expect(interp_code).to_equal(0)

step("Run the fixture through the hosted standalone native path")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect_sliced_fairness_output(native_out)
expect(native_code).to_equal(0)
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
- **Research:** [doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md](doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md)


</details>
