# Multicore Green Channel Struct Send Native Blocker

> This SSpec keeps the smaller current-source native blocker closed underneath the resumable-stepper fairness experiment: a `multicore_green` worker can send a plain struct payload through a channel, return, and let the main thread observe the expected value in a standalone native binary.

<!-- sdn-diagram:id=multicore_green_channel_struct_send_native_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_channel_struct_send_native_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_channel_struct_send_native_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_channel_struct_send_native_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Channel Struct Send Native Blocker

This SSpec keeps the smaller current-source native blocker closed underneath the resumable-stepper fairness experiment: a `multicore_green` worker can send a plain struct payload through a channel, return, and let the main thread observe the expected value in a standalone native binary.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-channel-struct-send-native-blocker |
| Category | Runtime / Native / Concurrency |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the smaller current-source native blocker closed underneath
the resumable-stepper fairness experiment: a `multicore_green` worker can send a
plain struct payload through a channel, return, and let the main thread observe
the expected value in a standalone native binary.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green channel struct send native regression

#### keeps the smaller pool-plus-struct-send path green

- Write the reduced pool channel struct-send probe
   - Expected: write_out equals ``
   - Expected: write_code equals `0`
- The reduced probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile still succeeds
   - Expected: compile_code equals `0`
- The standalone native probe returns the expected payload value
   - Expected: native_code equals `0`
- The tracker records the lower blocker as closed
   - Expected: tracker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the reduced pool channel struct-send probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out).to_equal("")
expect(write_code).to_equal(0)

step("The reduced probe still type-checks under the fresh debug compiler")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Hosted native compile still succeeds")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The standalone native probe returns the expected payload value")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/mcg_struct_send.out 2>&1; code=$?; cat /tmp/mcg_struct_send.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("value=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the lower blocker as closed")
val (tracker_out, tracker_code) = shell("cat doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_contain("Status: closed")
expect(tracker_out).to_contain("plain struct payload through a channel")
expect(tracker_out).to_contain("value=7")
expect(tracker_out).to_contain("EXIT=0")
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
