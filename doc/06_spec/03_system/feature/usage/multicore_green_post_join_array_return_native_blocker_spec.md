# Multicore Green Post-Join Array Return Native Blocker

> This SSpec keeps the narrower native blocker fixed after the resumable-stepper path itself became green. A `run_steppers` function that joins a `multicore_green` worker and then performs extra post-join string work before returning a local result array must stay on the native call path and return the expected array value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Post-Join Array Return Native Blocker

This SSpec keeps the narrower native blocker fixed after the resumable-stepper path itself became green. A `run_steppers` function that joins a `multicore_green` worker and then performs extra post-join string work before returning a local result array must stay on the native call path and return the expected array value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-post-join-array-return-native-blocker |
| Category | Runtime / Native / Concurrency |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md |
| Source | `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the narrower native blocker fixed after the resumable-stepper
path itself became green. A `run_steppers` function that joins a
`multicore_green` worker and then performs extra post-join string work before
returning a local result array must stay on the native call path and return the
expected array value.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green post join array return native regression

#### keeps post-join native array return on the compiled path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps post-join native array return on the compiled path
- Write the post-join array-return probe source
   - Expected: write_code equals `0`
- The generated probe still type-checks
   - Expected: check_code equals `0`
- Hosted native compile succeeds before the narrowed runtime crash
   - Expected: compile_code equals `0`
- The native probe runs after joining and returns the array
   - Expected: native_code equals `0`
- The tracker records the narrowed blocker as closed
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps post-join native array return on the compiled path")
step("Write the post-join array-return probe source")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The generated probe still type-checks")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Hosted native compile succeeds before the narrowed runtime crash")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe runs after joining and returns the array")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/mcg_post_join_array_return.out 2>&1; code=$?; cat /tmp/mcg_post_join_array_return.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("after_join=1")
expect(native_out).to_contain("result=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the narrowed blocker as closed")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: closed")
expect(blocker).to_contain("post-join")
expect(blocker).to_contain("EXIT=0")
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

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/05_design/multicore_green.md`
- **Research:** `doc/08_tracking/bug/multicore_green_post_join_array_return_native_blocker_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2c0956bd1d11d34403e0147b453006fa0a88af8319f631c04746ddfec2ed1ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2c0956bd1d11d34403e0147b453006fa0a88af8319f631c04746ddfec2ed1ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2c0956bd1d11d34403e0147b453006fa0a88af8319f631c04746ddfec2ed1ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps post-join native array return on the compiled path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
