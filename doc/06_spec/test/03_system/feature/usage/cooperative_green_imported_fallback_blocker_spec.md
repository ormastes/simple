# Cooperative Green Imported Fallback Blocker

> This SSpec pins the narrower compiled blocker behind the cooperative-green AOT crashes. Even a minimal value-only workload that calls `cooperative_green_spawn_value(...)` from an imported stdlib module runs in the interpreter, but current SMF and native artifacts fall back to interpreter lookup for that imported helper and then crash.

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

# Cooperative Green Imported Fallback Blocker

This SSpec pins the narrower compiled blocker behind the cooperative-green AOT crashes. Even a minimal value-only workload that calls `cooperative_green_spawn_value(...)` from an imported stdlib module runs in the interpreter, but current SMF and native artifacts fall back to interpreter lookup for that imported helper and then crash.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-imported-fallback |
| Category | Runtime / Native / SMF / Interpreter Fallback |
| Status | Known Blocker |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Research | doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md |
| Source | `test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the narrower compiled blocker behind the cooperative-green AOT
crashes. Even a minimal value-only workload that calls
`cooperative_green_spawn_value(...)` from an imported stdlib module runs in the
interpreter, but current SMF and native artifacts fall back to interpreter
lookup for that imported helper and then crash.

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

### cooperative green imported fallback blocker

#### keeps imported cooperative_green_spawn_value fallback failure explicit

- Write the minimal imported cooperative-green value-only fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Compile the fixture to SMF
   - Expected: smf_compile_code equals `0`
- Compile the fixture to native
   - Expected: native_compile_code equals `0`
- Run the fixture in the interpreter as the control
   - Expected: interp_code equals `0`
- Keep the current imported-function SMF fallback miss explicit
- Keep the current native crash explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
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

step("Keep the current imported-function SMF fallback miss explicit")
val (smf_out, smf_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(smf_out).to_contain("function `green_spawn_value` not found")
expect(smf_out.contains("cooperative_green_spawn_value_literal_pass=true")).to_be(false)
expect(smf_code).to_be_greater_than(0)

step("Keep the current native crash explicit")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out.contains("cooperative_green_spawn_value_literal_pass=true")).to_be(false)
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
