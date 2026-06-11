# Cooperative Green Spec Runner Mismatch

> This SSpec pins the current runner mismatch for green/cooperative queue APIs. The same minimal green-thread queue logic passes under `simple run`, but fails under `simple test`. Until that mismatch is fixed, hosted SimpleOS cooperative and multicore specs that assert green-queue behavior through the SSpec runner cannot be treated as green evidence.

<!-- sdn-diagram:id=cooperative_green_spec_runner_mismatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cooperative_green_spec_runner_mismatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cooperative_green_spec_runner_mismatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cooperative_green_spec_runner_mismatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Spec Runner Mismatch

This SSpec pins the current runner mismatch for green/cooperative queue APIs. The same minimal green-thread queue logic passes under `simple run`, but fails under `simple test`. Until that mismatch is fixed, hosted SimpleOS cooperative and multicore specs that assert green-queue behavior through the SSpec runner cannot be treated as green evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-spec-runner-mismatch |
| Category | Test Runner / Cooperative Green |
| Status | Known Blocker |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md |
| Source | `test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current runner mismatch for green/cooperative queue APIs.
The same minimal green-thread queue logic passes under `simple run`, but fails
under `simple test`. Until that mismatch is fixed, hosted SimpleOS cooperative
and multicore specs that assert green-queue behavior through the SSpec runner
cannot be treated as green evidence.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md

## Syntax

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl --mode=interpreter --clean
```

## Scenarios

### cooperative green spec runner mismatch

#### keeps the simple run vs simple test mismatch explicit

- Write the direct-run and SSpec probe fixtures
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(RUN_PATH, run_probe_source()) is true
   - Expected: rt_file_write_text(SPEC_PATH, spec_probe_source()) is true
- Verify the green-thread probe passes under simple run
   - Expected: run_code equals `0`
- Keep the current simple test mismatch explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the direct-run and SSpec probe fixtures")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(RUN_PATH, run_probe_source())).to_equal(true)
expect(rt_file_write_text(SPEC_PATH, spec_probe_source())).to_equal(true)

step("Verify the green-thread probe passes under simple run")
val (run_out, run_code) = shell(SIMPLE_BIN + " run " + RUN_PATH)
expect(run_out).to_contain("green_run_probe_pass=true")
expect(run_code).to_equal(0)

step("Keep the current simple test mismatch explicit")
val (test_out, test_code) = shell(SIMPLE_BIN + " test " + SPEC_PATH + " --mode=interpreter --clean")
expect(test_out).to_contain("FAILED")
expect(test_out).to_contain("green_probe_spec")
expect(test_code).to_be_greater_than(0)
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
- **Research:** [doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md](doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md)


</details>
