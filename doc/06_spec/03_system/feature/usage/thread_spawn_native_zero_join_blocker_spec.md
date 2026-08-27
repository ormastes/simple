# Thread Spawn Native Zero-Join Regression

> This SSpec regression-covers the standalone native `thread_spawn` fork-join path. A minimal top-level worker workload using the public `std.concurrent.thread` surface must stay green in the interpreter, SMF, and standalone native paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Spawn Native Zero-Join Regression

This SSpec regression-covers the standalone native `thread_spawn` fork-join path. A minimal top-level worker workload using the public `std.concurrent.thread` surface must stay green in the interpreter, SMF, and standalone native paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #thread-spawn-native-zero-join |
| Category | Runtime / Native / OS Thread |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md |
| Source | `test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec regression-covers the standalone native `thread_spawn` fork-join
path. A minimal top-level worker workload using the public
`std.concurrent.thread` surface must stay green in the interpreter, SMF, and
standalone native paths.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md

## Syntax

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple test test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl
thread_spawn native zero-join regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The fixture imports `thread_spawn` from `std.concurrent.thread`.
- The fixture stores public `ThreadHandle` values in an array.
- The interpreter control must print `thread_spawn_native_join_pass=true`.
- The SMF path must run the same generated source through bytecode.
- The standalone native path must run the same generated source through AOT.
- A checksum mismatch must exit nonzero rather than appearing as a speed win.
- The test command must honor `SIMPLE_BIN` for Docker-isolated runs.
- The Syntax block must not point at the stale `bin/release/simple` wrapper.
- This spec is OS-thread evidence, not cooperative-green or M:N evidence.
- `thread_spawn_with_args` remains covered by its focused ABI smoke path.
- The generated manual must keep the three execution modes visible.
- The tracker remains `current` until the broader Go-like runtime lane closes.

## Scenarios

### thread_spawn native zero-join regression

#### keeps interpreter, SMF, and standalone native fork-join green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps interpreter, SMF, and standalone native fork-join green
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
- Keep the standalone native path green
   - Expected: native_code equals `0`
- The tracker records the closed lower blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps interpreter, SMF, and standalone native fork-join green")
step("Write the minimal public thread_spawn fork-join fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, fixture_source())).to_equal(true)

step("Compile the fixture to SMF")
val (smf_compile_out, smf_compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " -o " + SMF_PATH)
expect(smf_compile_out).to_contain("Compiled")
expect(smf_compile_code).to_equal(0)

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Keep the interpreter control green on the public thread_spawn surface")
val (interp_out, interp_code) = shell(simple_bin() + " run " + SOURCE_PATH)
expect(interp_out).to_contain("thread_spawn_native_join_pass=true")
expect(interp_code).to_equal(0)

step("Keep the SMF bytecode path green")
val (smf_out, smf_code) = shell("timeout 20s " + simple_bin() + " " + SMF_PATH)
expect(smf_out).to_contain("thread_spawn_native_join_pass=true")
expect(smf_code).to_equal(0)

step("Keep the standalone native path green")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("thread_spawn_native_join_pass=true")
expect(native_code).to_equal(0)

step("The tracker records the closed lower blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: Closed")
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
- **Research:** `doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50ce277b1e19640649e027d9024a443dede7ed00ee902d6ba67d3e64cfad6716`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50ce277b1e19640649e027d9024a443dede7ed00ee902d6ba67d3e64cfad6716`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50ce277b1e19640649e027d9024a443dede7ed00ee902d6ba67d3e64cfad6716`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps interpreter, SMF, and standalone native fork-join green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
