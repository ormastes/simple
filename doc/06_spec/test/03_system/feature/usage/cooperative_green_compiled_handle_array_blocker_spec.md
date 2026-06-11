# Cooperative Green Compiled Handle-Array Blocker

> This SSpec keeps the remaining compiled cooperative-green function-spawn crash explicit. A minimal workload that stores multiple `GreenThreadHandle` values returned from `cooperative_green_spawn(worker)` runs in the interpreter and in SMF, but the standalone native artifact still crashes.

<!-- sdn-diagram:id=cooperative_green_compiled_handle_array_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cooperative_green_compiled_handle_array_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cooperative_green_compiled_handle_array_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cooperative_green_compiled_handle_array_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Compiled Handle-Array Blocker

This SSpec keeps the remaining compiled cooperative-green function-spawn crash explicit. A minimal workload that stores multiple `GreenThreadHandle` values returned from `cooperative_green_spawn(worker)` runs in the interpreter and in SMF, but the standalone native artifact still crashes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-compiled-handle-array |
| Category | Runtime / Native / SMF / Concurrency |
| Status | Known Blocker |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Research | doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md |
| Source | `test/03_system/feature/usage/cooperative_green_compiled_handle_array_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the remaining compiled cooperative-green function-spawn crash
explicit. A minimal workload that stores multiple `GreenThreadHandle` values
returned from `cooperative_green_spawn(worker)` runs in the interpreter and in
SMF, but the standalone native artifact still crashes.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md

## Syntax

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_compiled_handle_array_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### cooperative green compiled handle-array blocker

#### keeps the compiled cooperative_green_spawn handle-array crash explicit

- Write the minimal compiled cooperative-green handle-array fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Compile the fixture to SMF
   - Expected: smf_compile_code equals `0`
- Compile the fixture to native
   - Expected: native_compile_code equals `0`
- Run the fixture in the interpreter as the control
   - Expected: interp_code equals `0`
- Keep the fixed SMF path green
   - Expected: smf_code equals `0`
- Keep the remaining native crash explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the minimal compiled cooperative-green handle-array fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, fixture_source())).to_equal(true)

step("Compile the fixture to SMF")
val (smf_compile_out, smf_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " -o " + SMF_PATH)
expect(smf_compile_out).to_contain("Compiled")
expect(smf_compile_code).to_equal(0)

step("Compile the fixture to native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture in the interpreter as the control")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(interp_out).to_contain("cooperative_green_handle_array_pass=true")
expect(interp_code).to_equal(0)

step("Keep the fixed SMF path green")
val (smf_out, smf_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(smf_out).to_contain("cooperative_green_handle_array_pass=true")
expect(smf_code).to_equal(0)

step("Keep the remaining native crash explicit")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out.contains("cooperative_green_handle_array_pass=true")).to_be(false)
expect(native_code).to_be_greater_than(0)
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
