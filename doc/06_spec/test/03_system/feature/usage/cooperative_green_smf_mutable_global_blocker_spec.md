# Cooperative Green SMF Mutable Global Blocker

> This SSpec pins the root blocker behind the cooperative-green SMF profile rows: SMF execution currently crashes on a minimal module-level mutable counter. The implemented cooperative-green queue stores ready/done counters as Pure Simple mutable globals, so the SMF profile row must remain classified as a runtime blocker until this fixture exits successfully.

<!-- sdn-diagram:id=cooperative_green_smf_mutable_global_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cooperative_green_smf_mutable_global_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cooperative_green_smf_mutable_global_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cooperative_green_smf_mutable_global_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green SMF Mutable Global Blocker

This SSpec pins the root blocker behind the cooperative-green SMF profile rows: SMF execution currently crashes on a minimal module-level mutable counter. The implemented cooperative-green queue stores ready/done counters as Pure Simple mutable globals, so the SMF profile row must remain classified as a runtime blocker until this fixture exits successfully.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-smf-mutable-global |
| Category | Runtime / SMF / Concurrency |
| Status | Active Blocker |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/cooperative_green_smf_mutable_global_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the root blocker behind the cooperative-green SMF profile rows:
SMF execution currently crashes on a minimal module-level mutable counter. The
implemented cooperative-green queue stores ready/done counters as Pure Simple
mutable globals, so the SMF profile row must remain classified as a runtime
blocker until this fixture exits successfully.

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
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_smf_mutable_global_blocker_spec.spl --mode=interpreter --clean
```

## Examples

- The minimal source uses a module-level mutable `COUNT`.
- Source checking and SMF compilation must succeed.
- Running the SMF artifact currently exits nonzero, proving the runtime blocker
  is still real.
- When the SMF artifact exits `0`, this spec must be inverted and the
  cooperative-green SMF profile rows can stop reporting the mutable-global
  blocker.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/feature/usage/cooperative_green_smf_mutable_global_blocker_spec.spl
Cooperative green SMF mutable global blocker PASSED
Files: 1
Passed: 1
Failed: 0
```

## Scenarios

### Cooperative green SMF mutable-global blocker

#### keeps the minimal mutable-global SMF crash visible

- Create the minimal mutable-global fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, mutable_global_fixture_source()) is true
- Check and compile the fixture to SMF
   - Expected: check_code equals `0`
   - Expected: compile_code equals `0`
- Run the SMF artifact and keep the blocker classified


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create the minimal mutable-global fixture")
val (mkdir_stdout, mkdir_stderr, mkdir_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + BUILD_DIR])
expect(process_output(mkdir_stdout, mkdir_stderr).len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, mutable_global_fixture_source())).to_equal(true)

step("Check and compile the fixture to SMF")
val (check_stdout, check_stderr, check_code) = rt_process_run(SIMPLE_BIN, ["check", SOURCE_PATH])
expect(process_output(check_stdout, check_stderr)).to_contain("OK")
expect(check_code).to_equal(0)
val (compile_stdout, compile_stderr, compile_code) = rt_process_run(SIMPLE_BIN, ["compile", SOURCE_PATH, "-o", SMF_PATH])
expect(process_output(compile_stdout, compile_stderr)).to_contain("Compiled")
expect(compile_code).to_equal(0)

step("Run the SMF artifact and keep the blocker classified")
val (run_stdout, run_stderr, run_code) = rt_process_run(SIMPLE_BIN, [SMF_PATH])
expect(process_output(run_stdout, run_stderr).len()).to_be_greater_than(-1)
expect(run_code).to_be_less_than(0)
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
