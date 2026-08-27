# Multicore Green Channel Struct Send Native Blocker

> This SSpec keeps the smaller current-source native blocker closed underneath the resumable-stepper fairness experiment: a `multicore_green` worker can send a plain struct payload through a channel, return, and let the main thread observe the expected value in a standalone native binary.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the smaller pool-plus-struct-send path green
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

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the smaller pool-plus-struct-send path green")
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

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/05_design/multicore_green.md`
- **Research:** `doc/08_tracking/bug/multicore_green_channel_struct_send_native_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b03c63b408cec6f3aaf4d7968b6fd304432517896b8cf7416092890ae6e4dc63`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b03c63b408cec6f3aaf4d7968b6fd304432517896b8cf7416092890ae6e4dc63`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b03c63b408cec6f3aaf4d7968b6fd304432517896b8cf7416092890ae6e4dc63`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_channel_struct_send_native_blocker_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the smaller pool-plus-struct-send path green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
