# SMF Runtime-Pool Closure Lookup Blocker

> This SSpec pins the narrow SMF runtime-pool blocker for `multicore_green_spawn`. Direct SMF submission of `multicore_green_spawn(\: worker())` can pass, but the profile-generated wrapper shape still fails when runtime-pool worker threads call back into the SMF interpreter.

<!-- sdn-diagram:id=smf_runtime_pool_closure_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_runtime_pool_closure_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_runtime_pool_closure_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_runtime_pool_closure_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Runtime-Pool Closure Lookup Blocker

This SSpec pins the narrow SMF runtime-pool blocker for `multicore_green_spawn`. Direct SMF submission of `multicore_green_spawn(\: worker())` can pass, but the profile-generated wrapper shape still fails when runtime-pool worker threads call back into the SMF interpreter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-smf-runtime-pool-closure |
| Category | Runtime / SMF / Concurrency |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/smf_runtime_pool_closure_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the narrow SMF runtime-pool blocker for `multicore_green_spawn`.
Direct SMF submission of `multicore_green_spawn(\: worker())` can pass, but the
profile-generated wrapper shape still fails when runtime-pool worker threads
call back into the SMF interpreter.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the blocker contract:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/smf_runtime_pool_closure_blocker_spec.spl --mode=interpreter --clean
```

## Examples

- The fixture compiles to SMF successfully.
- The fixture configures runtime-pool parallelism.
- The fixture fails today with `function not found: spawn_worker`.
- The blocker is resolved only when the same fixture exits successfully and
  prints `wrapper_smf_pool_pass=true`.

## Current Failure Shape

The checked profile script generates wrapper helpers so the benchmark can keep
the spawn expression compact and comparable across parallel/fanout sections:

```simple
fn worker() -> i64:
    42

fn spawn_worker() -> MulticoreGreenHandle:
    multicore_green_spawn(\: worker())
```

The direct shape below is intentionally not enough regression coverage because
it already passes on this checkout:

```simple
val handle = multicore_green_spawn(\: worker())
```

This spec therefore exercises the wrapper shape and expects the current SMF
loader/runtime-pool boundary to fail in a controlled way. That keeps failed SMF
rows out of M:N evidence while still proving that the blocker is understood.

## Expected Runtime Output

The SMF process should print runtime-pool setup evidence before failing:

```text
multicore_green_parallelism = 2/2
rt_interp_call: function not found: spawn_worker
```

It must not print:

```text
wrapper_smf_pool_pass=true
```

until worker-thread `rt_interp_call` can resolve the SMF module function table.

## Resolution Contract

When the blocker is fixed, update this spec in the same commit that updates the
profile report contract:

- keep the wrapper-shaped fixture;
- require exit code `0`;
- require `wrapper_smf_pool_pass=true`;
- require the checked-in cross-language report to contain valid SMF
  multicore-green rows for the parallel and fanout sections;
- close `doc/08_tracking/bug/smf_runtime_pool_closure_lookup_2026-06-07.md`;
- remove the temporary allowance for `SMF runtime-pool closure lookup blocker`
  from `test/05_perf/profile_scripts/profile_report_contract_test.shs`.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/feature/usage/smf_runtime_pool_closure_blocker_spec.spl
[1/1] test/03_system/feature/usage/smf_runtime_pool_closure_blocker_spec.spl PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The blocker document must identify the wrapper-shape failure.
- The blocker document must name `INTERP_FUNCTIONS` and `interp_call_handler`.
- The executable fixture must use `spawn_worker() -> multicore_green_spawn(\: worker())`.
- The fixture must fail today before it can be counted as SMF M:N evidence.
- The failure must mention `function not found: spawn_worker`.
- The fixture must be flipped from expected failure to expected pass when SMF
  worker-thread function lookup is fixed.
- The direct worker shape must not replace this wrapper-shaped regression.

## Scenarios

### SMF runtime-pool closure lookup blocker

#### keeps the wrapper-shaped multicore-green SMF failure executable

- Write the minimal wrapper-shaped multicore-green fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, blocker_fixture_source()) is true
- Compile the fixture to SMF
   - Expected: compile_code equals `0`
   - Expected: exists_code equals `0`
- Run the SMF fixture and capture the current blocker failure
- Verify the blocker document describes the same narrow failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the minimal wrapper-shaped multicore-green fixture")
val (_mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, blocker_fixture_source())).to_equal(true)

step("Compile the fixture to SMF")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " -o " + SMF_PATH)
expect(compile_code).to_equal(0)
val (_exists_out, exists_code) = shell("test -f " + SMF_PATH)
expect(exists_code).to_equal(0)

step("Run the SMF fixture and capture the current blocker failure")
val (run_out, run_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(run_code).to_be_greater_than(0)
expect(run_out).to_contain("function not found: spawn_worker")
expect(run_out).to_contain("multicore_green_parallelism")

step("Verify the blocker document describes the same narrow failure")
val blocker = read_text("doc/08_tracking/bug/smf_runtime_pool_closure_lookup_2026-06-07.md")
expect(blocker).to_contain("function not found: spawn_worker")
expect(blocker).to_contain("spawn_worker()")
expect(blocker).to_contain("INTERP_FUNCTIONS")
expect(blocker).to_contain("interp_call_handler")
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
