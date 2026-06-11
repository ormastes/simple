# Thread Spawn Native Zero-Join Blocker

> This SSpec pins the current standalone native `thread_spawn` fork-join blocker. A minimal top-level worker workload using the public `std.concurrent.thread` surface must stay green in the interpreter and SMF paths, while the current standalone native artifact still reproduces the zero-result join failure.

<!-- sdn-diagram:id=thread_spawn_native_zero_join_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_spawn_native_zero_join_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_spawn_native_zero_join_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_spawn_native_zero_join_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Spawn Native Zero-Join Blocker

This SSpec pins the current standalone native `thread_spawn` fork-join blocker. A minimal top-level worker workload using the public `std.concurrent.thread` surface must stay green in the interpreter and SMF paths, while the current standalone native artifact still reproduces the zero-result join failure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #thread-spawn-native-zero-join |
| Category | Runtime / Native / OS Thread |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Research | doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md |
| Source | `test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current standalone native `thread_spawn` fork-join blocker.
A minimal top-level worker workload using the public `std.concurrent.thread`
surface must stay green in the interpreter and SMF paths, while the current
standalone native artifact still reproduces the zero-result join failure.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md

## Syntax

```sh
bin/release/simple test test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### thread_spawn native zero-join blocker

#### keeps interpreter and SMF green while pinning the current standalone native join failure

- Write the minimal public thread_spawn fork-join fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Compile the fixture to SMF
   - Expected: smf_compile_code equals `0`
- Compile the fixture to standalone native
   - Expected: native_compile_code equals `0`
- Keep the interpreter control green on the public thread_spawn surface
   - Expected: interp_code equals `0`
- Keep the SMF bytecode path green
   - Expected: smf_code equals `0`
- Pin the current standalone native zero-result join failure
   - Expected: native_code equals `74`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the minimal public thread_spawn fork-join fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, fixture_source())).to_equal(true)

step("Compile the fixture to SMF")
val (smf_compile_out, smf_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " -o " + SMF_PATH)
expect(smf_compile_out).to_contain("Compiled")
expect(smf_compile_code).to_equal(0)

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Keep the interpreter control green on the public thread_spawn surface")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(interp_out).to_contain("thread_spawn_native_join_pass=true")
expect(interp_code).to_equal(0)

step("Keep the SMF bytecode path green")
val (smf_out, smf_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(smf_out).to_contain("thread_spawn_native_join_pass=true")
expect(smf_code).to_equal(0)

step("Pin the current standalone native zero-result join failure")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("checksum_mismatch total=0 expected=14")
expect(native_code).to_equal(74)
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
- **Research:** [doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md](doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md)


</details>
