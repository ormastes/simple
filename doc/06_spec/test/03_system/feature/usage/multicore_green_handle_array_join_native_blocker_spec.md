<<<<<<< Conflict 1 of 1
%%%%%%% Changes from base to side #1
+# Multicore Green Handle Array Join Native Regression
+
+> This SSpec regression-covers the hosted-native helper path where an inferred empty local handle array is populated with `append`, iterated, and joined.
+
+<!-- sdn-diagram:id=multicore_green_handle_array_join_native_blocker_spec.arch -->
+<details class="sdn-source">
+<summary>SDN source</summary>
+
+```sdn id=multicore_green_handle_array_join_native_blocker_spec.arch hash=sha256:auto render=ascii
+@layout dag
+@direction LR
+
+multicore_green_handle_array_join_native_blocker_spec -> std
+```
+
+</details>
+
+<details class="sdn-ascii" open>
+<summary>Diagram</summary>
+
+```ascii generated-from=multicore_green_handle_array_join_native_blocker_spec.arch hash=sha256:auto
+# run: simple md-diagram-update
+```
+
+</details>
+<!-- sdn-diagram:end -->
+
+| Tests | Active | Skipped | Pending |
+|-------|--------|---------|--------:|
+| 1 | 1 | 0 | 0 |
+
+<details>
+<summary>Full Scenario Manual</summary>
+
+# Multicore Green Handle Array Join Native Regression
+
+This SSpec regression-covers the hosted-native helper path where an inferred empty local handle array is populated with `append`, iterated, and joined.
+
+## At a Glance
+
+| Field | Value |
+|-------|-------|
+| Feature IDs | #multicore-green-handle-array-join-native-blocker |
+| Category | Runtime / Native / Concurrency |
+| Status | Regression |
+| Requirements | doc/02_requirements/feature/multicore_green.md |
+| Plan | doc/03_plan/sys_test/multicore_green.md |
+| Design | doc/05_design/multicore_green.md |
+| Research | doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md |
+| Source | `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl` |
+| Updated | 2026-06-01 |
+| Generator | `simple spipe-docgen` (Simple) |
+
+## Overview
+
+This SSpec regression-covers the hosted-native helper path where an inferred
+empty local handle array is populated with `append`, iterated, and joined.
+
+## Requirements
+
+**Requirements:** doc/02_requirements/feature/multicore_green.md
+
+## Plan
+
+**Plan:** doc/03_plan/sys_test/multicore_green.md
+
+## Design
+
+**Design:** doc/05_design/multicore_green.md
+
+## Research
+
+**Research:** doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md
+
+## Syntax
+
+```sh
+bin/release/simple test test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl --mode=interpreter --clean
+```
+
+## Scenarios
+
+### multicore green handle-array join native regression
+
+#### keeps local handle-array iteration and join native
+
+- Write the reduced handle-array join probe
+   - Expected: write_code equals `0`
+- The reduced probe still type-checks under the fresh debug compiler
+   - Expected: check_code equals `0`
+- Hosted native compile succeeds for the helper loop
+   - Expected: compile_code equals `0`
+- The native probe joins the indexed handles and returns the worker result
+   - Expected: native_code equals `0`
+- The tracker records the closed lower blocker
+   - Expected: blocker_code equals `0`
+
+
+<details>
+<summary>Executable SSpec</summary>
+
+Runnable source: 22 lines folded for reproduction.
+Reproduction: this block contains the complete executable scenario source.
+
+```simple
+step("Write the reduced handle-array join probe")
+val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
+expect(write_code).to_equal(0)
+
+step("The reduced probe still type-checks under the fresh debug compiler")
+val (_, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
+expect(check_code).to_equal(0)
+
+step("Hosted native compile succeeds for the helper loop")
+val (_, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
+expect(compile_code).to_equal(0)
+
+step("The native probe joins the indexed handles and returns the worker result")
+val (native_out, native_code) = shell("sh -c './" + NATIVE_PATH + " >/tmp/mcg_handle_array_join_probe.out 2>&1; code=$?; cat /tmp/mcg_handle_array_join_probe.out; echo EXIT=$code'")
+expect(native_code).to_equal(0)
+expect(native_out).to_contain("result=7")
+expect(native_out).to_contain("EXIT=0")
+
+step("The tracker records the closed lower blocker")
+val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md")
+expect(blocker_code).to_equal(0)
+expect(blocker).to_contain("Status: closed")
+```
+
+</details>
+
+## Scenario Summary
+
+| Metric | Count |
+|--------|------:|
+| Total scenarios | 1 |
+| Active scenarios | 1 |
+| Slow scenarios | 0 |
+| Skipped scenarios | 0 |
+| Pending scenarios | 0 |
+
+
+## Related Documentation
+
+- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
+- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
+- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
+- **Research:** [doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md](doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md)
+
+
+</details>
+++++++ Contents of side #2
# Multicore Green Handle Array Join Native Blocker

> This SSpec pins the current lower hosted-native blocker beneath the remaining `multicore_green` resumable-stepper lane. The smaller by-value struct-array blocker is closed; the active failure is now local handle-array iteration and join inside a helper.

<!-- sdn-diagram:id=multicore_green_handle_array_join_native_blocker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_handle_array_join_native_blocker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_handle_array_join_native_blocker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_handle_array_join_native_blocker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Handle Array Join Native Blocker

This SSpec pins the current lower hosted-native blocker beneath the remaining `multicore_green` resumable-stepper lane. The smaller by-value struct-array blocker is closed; the active failure is now local handle-array iteration and join inside a helper.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-handle-array-join-native-blocker |
| Category | Runtime / Native / Concurrency |
| Status | Blocked |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the current lower hosted-native blocker beneath the remaining
`multicore_green` resumable-stepper lane. The smaller by-value struct-array
blocker is closed; the active failure is now local handle-array iteration and
join inside a helper.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md

## Syntax

```sh
bin/release/simple test test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green handle-array join native blocker

#### keeps the lower hosted-native handle-array failure explicit

- Write the reduced handle-array join probe
   - Expected: write_code equals `0`
- The reduced probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile still succeeds before the runtime failure
   - Expected: compile_code equals `0`
- The native probe still returns the lower handle-array mismatch boundary
   - Expected: native_code equals `0`
- The tracker records the current lower blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write the reduced handle-array join probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The reduced probe still type-checks under the fresh debug compiler")
val (_, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)

step("Hosted native compile still succeeds before the runtime failure")
val (_, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)

step("The native probe still returns the lower handle-array mismatch boundary")
val (native_out, native_code) = shell("sh -c './" + NATIVE_PATH + " >/tmp/mcg_handle_array_join_probe.out 2>&1; code=$?; cat /tmp/mcg_handle_array_join_probe.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("EXIT=12")

step("The tracker records the current lower blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: open")
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
- **Research:** [doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md](doc/08_tracking/bug/multicore_green_handle_array_join_native_blocker_2026-06-11.md)


</details>
>>>>>>> Conflict 1 of 1 ends
