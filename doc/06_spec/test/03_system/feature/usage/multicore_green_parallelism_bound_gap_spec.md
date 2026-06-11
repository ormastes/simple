# Multicore Green Parallelism Bound Gap

> This SSpec pins the remaining hosted multicore-green `GOMAXPROCS`-style bound gap. After the compensation-worker fix, blocked work can progress, but the hosted runtime still grows pool width beyond the requested parallelism under pure CPU saturation.

<!-- sdn-diagram:id=multicore_green_parallelism_bound_gap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_parallelism_bound_gap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_parallelism_bound_gap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_parallelism_bound_gap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Parallelism Bound Gap

This SSpec pins the remaining hosted multicore-green `GOMAXPROCS`-style bound gap. After the compensation-worker fix, blocked work can progress, but the hosted runtime still grows pool width beyond the requested parallelism under pure CPU saturation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-parallelism-bound-gap |
| Category | Runtime / Hosted / Multicore Green |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the remaining hosted multicore-green `GOMAXPROCS`-style bound
gap. After the compensation-worker fix, blocked work can progress, but the
hosted runtime still grows pool width beyond the requested parallelism under
pure CPU saturation.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green parallelism bound gap

#### keeps the hosted oversubscription gap explicit across source-run and native artifacts

- Prepare the native output directory for the checked-in parallelism-bound fixture
   - Expected: mkdir_code equals `0`
- Compile the fixture to standalone native
   - Expected: native_compile_code equals `0`
- Run the fixture through the hosted source path
   - Expected: interp_code equals `0`
- Run the fixture through the hosted standalone native path
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare the native output directory for the checked-in parallelism-bound fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture through the hosted source path")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(interp_out).to_contain("parallelism_before=2")
expect(interp_out).to_contain("parallelism_after_submit=3")
expect(interp_out).to_contain("total=10")
expect(interp_code).to_equal(0)

step("Run the fixture through the hosted standalone native path")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("parallelism_before=2")
expect(native_out).to_contain("parallelism_after_submit=3")
expect(native_out).to_contain("total=10")
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
