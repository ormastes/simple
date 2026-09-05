# Cooperative Green Imported Fallback Native Regression

> This SSpec keeps the imported cooperative-green value helper fixed across the interpreter, SMF, and standalone native paths. A minimal value-only workload that calls `cooperative_green_spawn_value(...)` from an imported stdlib module must compile and run successfully on all three paths.

<!-- sdn-diagram:id=cooperative_green_imported_fallback_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cooperative_green_imported_fallback_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cooperative_green_imported_fallback_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cooperative_green_imported_fallback_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Imported Fallback Native Regression

This SSpec keeps the imported cooperative-green value helper fixed across the interpreter, SMF, and standalone native paths. A minimal value-only workload that calls `cooperative_green_spawn_value(...)` from an imported stdlib module must compile and run successfully on all three paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-imported-fallback-native |
| Category | Runtime / Native / Interpreter Fallback |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Research | doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md |
| Source | `test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the imported cooperative-green value helper fixed across the
interpreter, SMF, and standalone native paths. A minimal value-only workload
that calls `cooperative_green_spawn_value(...)` from an imported stdlib module
must compile and run successfully on all three paths.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md

## Syntax

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### cooperative green imported fallback native regression

#### keeps imported cooperative_green_spawn_value working across interpreter, SMF, and native

- Write the minimal imported cooperative-green value-only fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Compile the fixture to SMF
   - Expected: smf_compile_code equals `0`
- Compile the fixture to native
   - Expected: native_compile_code equals `0`
- Run the fixture in the interpreter as the control
   - Expected: interp_code equals `0`
- Keep the fixed imported-function SMF path green
   - Expected: smf_code equals `0`
- Keep the standalone native path green
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the minimal imported cooperative-green value-only fixture")
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
expect(interp_out).to_contain("cooperative_green_spawn_value_literal_pass=true")
expect(interp_code).to_equal(0)

step("Keep the fixed imported-function SMF path green")
val (smf_out, smf_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(smf_out).to_contain("cooperative_green_spawn_value_literal_pass=true")
expect(smf_code).to_equal(0)

step("Keep the standalone native path green")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("cooperative_green_spawn_value_literal_pass=true")
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
- **Research:** [doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md](doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md)


</details>
