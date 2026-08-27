# Multicore Green Explicit Safepoint Fairness Regression

> This SSpec proves a hosted runtime-pool safepoint hook can make a concrete safepoint-assisted handoff without claiming automatic compiler preemption. With hosted parallelism pinned to `1`, a long `multicore_green_spawn` closure that explicitly calls `multicore_green_safepoint()` can let later quick tasks finish during the first observation window on the standalone native path, and the runtime counters show the submitted/completed/pending state for that same run.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Explicit Safepoint Fairness Regression

This SSpec proves a hosted runtime-pool safepoint hook can make a concrete safepoint-assisted handoff without claiming automatic compiler preemption. With hosted parallelism pinned to `1`, a long `multicore_green_spawn` closure that explicitly calls `multicore_green_safepoint()` can let later quick tasks finish during the first observation window on the standalone native path, and the runtime counters show the submitted/completed/pending state for that same run.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-safepoint-fairness |
| Category | Runtime / Hosted / Multicore Green |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec proves a hosted runtime-pool safepoint hook can make a concrete
safepoint-assisted handoff without claiming automatic compiler preemption.
With hosted parallelism pinned to `1`, a long
`multicore_green_spawn` closure that explicitly calls
`multicore_green_safepoint()` can let later quick tasks finish during the first
observation window on the standalone native path, and the runtime counters show
the submitted/completed/pending state for that same run.

Raw `thread_yield()` remains insufficient; this regression is the runtime
target for future compiler-inserted loop safepoints.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.spl --mode=interpreter --clean

The spec itself runs in interpreter mode, but its behavioral proof compiles and
executes `test/fixtures/concurrency/multicore_green_safepoint_fairness_fixture.spl`
as a standalone native binary because the runtime worker pool is native-hosted.
```

## Scenarios

### multicore green explicit safepoint fairness

#### lets a quick task run when a long native pool closure polls the safepoint hook

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lets a quick task run when a long native pool closure polls the safepoint hook
- Prepare the native output directory for the safepoint fairness fixture
   - Expected: mkdir_code equals `0`
- The fixture type-checks with the public safepoint API
   - Expected: check_code equals `0`
- Compile the fixture to standalone native
   - Expected: native_compile_code equals `0`
- Run the fixture through the hosted standalone native path
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lets a quick task run when a long native pool closure polls the safepoint hook")
step("Prepare the native output directory for the safepoint fairness fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)

step("The fixture type-checks with the public safepoint API")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture through the hosted standalone native path")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("parallelism_before=1")
expect(native_out).to_contain("submitted_before=0")
expect(native_out).to_contain("quick_a_done_during_spin=true")
expect(native_out).to_contain("quick_b_done_during_spin=true")
expect(native_out).to_contain("submitted_during_spin=3")
expect(native_out).to_contain("completed_during_spin=2")
expect(native_out).to_contain("submitted_after_join=3")
expect(native_out).to_contain("completed_after_join=3")
expect(native_out).to_contain("pending_after_join=0")
expect(native_out).to_contain("busy_after_join=0")
expect(native_out).to_contain("total=20")
expect(native_code).to_equal(0)
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
- **Research:** `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82059a6a44aea34a76710830b2873ea361622acf7bb8b1ea73a747d6e33fb336`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82059a6a44aea34a76710830b2873ea361622acf7bb8b1ea73a747d6e33fb336`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82059a6a44aea34a76710830b2873ea361622acf7bb8b1ea73a747d6e33fb336`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets a quick task run when a long native pool closure polls the safepoint hook' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
