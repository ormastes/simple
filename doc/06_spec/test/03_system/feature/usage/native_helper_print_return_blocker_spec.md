# Native Helper Print Return Blocker

> This SSpec pins the current lower native blocker beneath the hosted `multicore_green` fairness lane. A plain helper that calls `println("ok")` and then returns a later value still returns `3` on current-source native.

<!-- sdn-diagram:id=native_helper_print_return_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_helper_print_return_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_helper_print_return_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_helper_print_return_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Helper Print Return Blocker

This SSpec pins the current lower native blocker beneath the hosted `multicore_green` fairness lane. A plain helper that calls `println("ok")` and then returns a later value still returns `3` on current-source native.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-helper-print-return-blocker |
| Category | Runtime / Native / Seed |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_helper_print_return_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current lower native blocker beneath the hosted
`multicore_green` fairness lane. A plain helper that calls `println("ok")` and
then returns a later value still returns `3` on current-source native.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_helper_print_return_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### native helper print return blocker

#### keeps the lower native helper-return bug explicit

- Write the reduced helper-print probe source
   - Expected: write_code equals `0`
- The reduced probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile succeeds before the lower runtime mismatch
   - Expected: compile_code equals `0`
- The native probe still returns the wrong post-print helper value
   - Expected: native_code equals `0`
- The tracker records the same narrowed helper-return blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the reduced helper-print probe source")
val (_, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The reduced probe still type-checks under the fresh debug compiler")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Hosted native compile succeeds before the lower runtime mismatch")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe still returns the wrong post-print helper value")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_helper_print_return.out 2>&1; code=$?; cat /tmp/native_helper_print_return.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("before")
expect(native_out).to_contain("after=3")
expect(native_out).to_contain("EXIT=175")

step("The tracker records the same narrowed helper-return blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: open")
expect(blocker).to_contain("calls `println(\"ok\")`")
expect(blocker).to_contain("after=3")
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
- **Research:** [doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md](doc/08_tracking/bug/native_helper_print_return_blocker_2026-06-11.md)


</details>
