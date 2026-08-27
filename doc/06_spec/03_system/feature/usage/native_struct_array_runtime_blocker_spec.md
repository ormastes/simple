# Native Struct Array Runtime Regression

> This SSpec keeps the closed lower hosted-native struct-array regression covered. A direct native array of by-value structs is green again on current-source seed/native and should stay that way while the higher `multicore_green` handle-array blocker is fixed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Struct Array Runtime Regression

This SSpec keeps the closed lower hosted-native struct-array regression covered. A direct native array of by-value structs is green again on current-source seed/native and should stay that way while the higher `multicore_green` handle-array blocker is fixed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-struct-array-runtime-blocker |
| Category | Runtime / Native / Collections |
| Status | Regression Covered |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the closed lower hosted-native struct-array regression
covered. A direct native array of by-value structs is green again on
current-source seed/native and should stay that way while the higher
`multicore_green` handle-array blocker is fixed.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md

## Syntax

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl
native struct array runtime regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The fixture writes a direct array of by-value `Boxed` structs.
- The same generated source is checked and compiled by `SIMPLE_BIN`.
- The standalone native output must contain `result=7`.
- The standalone native exit marker must contain `EXIT=0`.
- The test command must honor `SIMPLE_BIN` for Docker-isolated runs.
- The Syntax block must not point at the stale `bin/release/simple` wrapper.
- The closed native struct-array tracker must remain linked.

## Scenarios

### native struct array runtime regression

#### keeps the closed native struct-array path green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the closed native struct-array path green
- Write the direct struct-array probe source
   - Expected: write_code equals `0`
- The generated probe still type-checks under the fresh debug compiler
   - Expected: check_code equals `0`
- Hosted native compile still succeeds
   - Expected: compile_code equals `0`
- The native probe now returns the expected result boundary
   - Expected: native_code equals `0`
- The tracker records the lower blocker as closed
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the closed native struct-array path green")
step("Write the direct struct-array probe source")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("The generated probe still type-checks under the fresh debug compiler")
val (_, check_code) = shell(simple_bin() + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)

step("Hosted native compile still succeeds")
val (_, compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)

step("The native probe now returns the expected result boundary")
val (native_out, native_code) = shell("sh -c './" + NATIVE_PATH + " >/tmp/native_struct_array_probe.out 2>&1; code=$?; cat /tmp/native_struct_array_probe.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("result=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the lower blocker as closed")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: closed")
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
- **Research:** `doc/08_tracking/bug/native_struct_array_runtime_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f136726b1a4160e5f6cb70c0b3ba7480af5336fcd1db1474cbac75bb36d9527`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f136726b1a4160e5f6cb70c0b3ba7480af5336fcd1db1474cbac75bb36d9527`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f136726b1a4160e5f6cb70c0b3ba7480af5336fcd1db1474cbac75bb36d9527`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/native_struct_array_runtime_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/native_struct_array_runtime_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/native_struct_array_runtime_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the closed native struct-array path green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
