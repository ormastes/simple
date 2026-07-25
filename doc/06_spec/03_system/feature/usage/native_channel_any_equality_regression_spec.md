# Native Channel Any Equality Regression

> This SSpec regression-covers the lower direct channel path that previously miscompared integer payloads after `recv()`: a plain main-thread `channel_new() -> send(7) -> recv() -> == 7` roundtrip now stays green on the current-source debug seed.

<!-- sdn-diagram:id=native_channel_any_equality_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_channel_any_equality_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_channel_any_equality_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_channel_any_equality_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Channel Any Equality Regression

This SSpec regression-covers the lower direct channel path that previously miscompared integer payloads after `recv()`: a plain main-thread `channel_new() -> send(7) -> recv() -> == 7` roundtrip now stays green on the current-source debug seed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-channel-any-equality-regression |
| Category | Runtime / Native / Concurrency |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_channel_any_equality_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec regression-covers the lower direct channel path that previously
miscompared integer payloads after `recv()`: a plain main-thread
`channel_new() -> send(7) -> recv() -> == 7` roundtrip now stays green on the
current-source debug seed.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_channel_any_equality_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native channel any equality regression

#### keeps direct channel integer roundtrip equality green

- Write the direct channel equality probe
   - Expected: write_out equals ``
   - Expected: write_code equals `0`
- Source-run now keeps integer equality after recv()
   - Expected: run_code equals `0`
   - Expected: run_out equals ``
- Hosted native compile still succeeds
   - Expected: compile_code equals `0`
- The standalone native probe now exits cleanly on the direct channel path
   - Expected: native_code equals `0`
   - Expected: native_out equals ``
- The tracker records direct channel equality as green and the remaining blocker above the pool-worker path
   - Expected: tracker_code equals `0`
   - Expected: tracker_out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the direct channel equality probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out).to_equal("")
expect(write_code).to_equal(0)

step("Source-run now keeps integer equality after recv()")
val (run_out, run_code) = shell("sh -c '" + SIMPLE_BIN + " run " + SOURCE_PATH + " > /tmp/native_channel_any_eq_source.out 2>&1 && grep -q 7 /tmp/native_channel_any_eq_source.out && grep -q true /tmp/native_channel_any_eq_source.out'")
expect(run_code).to_equal(0)
expect(run_out).to_equal("")

step("Hosted native compile still succeeds")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The standalone native probe now exits cleanly on the direct channel path")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " > /tmp/native_channel_any_eq.out 2>&1 && grep -q 7 /tmp/native_channel_any_eq.out && grep -q true /tmp/native_channel_any_eq.out'")
expect(native_code).to_equal(0)
expect(native_out).to_equal("")

step("The tracker records direct channel equality as green and the remaining blocker above the pool-worker path")
val (tracker_out, tracker_code) = shell("sh -c 'grep -q \"direct main-thread\" doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md && grep -q \"now green again\" doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md && grep -q \"hosted pool worker sends payloads\" doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md'")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_equal("")
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
- **Research:** [doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md](doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md)


</details>
