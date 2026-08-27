# Multicore Green Parallelism Bound Regression

> This SSpec keeps hosted multicore-green `GOMAXPROCS`-style bound behavior under regression coverage. After the blocking-aware compensation fix, blocked work can still progress, but pure CPU saturation must keep pool width at the requested parallelism.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Parallelism Bound Regression

This SSpec keeps hosted multicore-green `GOMAXPROCS`-style bound behavior under regression coverage. After the blocking-aware compensation fix, blocked work can still progress, but pure CPU saturation must keep pool width at the requested parallelism.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-parallelism-bound-gap |
| Category | Runtime / Hosted / Multicore Green |
| Status | Regression Coverage |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps hosted multicore-green `GOMAXPROCS`-style bound behavior under
regression coverage. After the blocking-aware compensation fix, blocked work
can still progress, but pure CPU saturation must keep pool width at the
requested parallelism.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green parallelism bound regression

#### keeps hosted CPU saturation bounded across source-run and native artifacts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps hosted CPU saturation bounded across source-run and native artifacts
- Prepare the native output directory for the checked-in parallelism-bound fixture
   - Expected: mkdir_code equals `0`
- Compile the fixture to standalone native
   - Expected: native_compile_code equals `0`
- Run the fixture through the hosted source path
   - Expected: interp_code equals `0`
- Run the fixture through the hosted standalone native path
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps hosted CPU saturation bounded across source-run and native artifacts")
step("Prepare the native output directory for the checked-in parallelism-bound fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture through the hosted source path")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(interp_out).to_contain("parallelism_zero_clamped=1")
expect(interp_out).to_contain("parallelism_negative_clamped=1")
expect(interp_out).to_contain("parallelism_before=2")
expect(interp_out).to_contain("parallelism_after_submit=2")
expect(interp_out).to_contain("parallelism_after_join=2")
expect(interp_out).to_contain("total=10")
expect(interp_code).to_equal(0)

step("Run the fixture through the hosted standalone native path")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("parallelism_zero_clamped=1")
expect(native_out).to_contain("parallelism_negative_clamped=1")
expect(native_out).to_contain("parallelism_before=2")
expect(native_out).to_contain("parallelism_after_submit=2")
expect(native_out).to_contain("parallelism_after_join=2")
expect(native_out).to_contain("total=10")
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

- Canonical SPipe generation for source `63de453f649fe038eb9f0a039cbfe79942843abc46c7de9e02bb4e41e7f860e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63de453f649fe038eb9f0a039cbfe79942843abc46c7de9e02bb4e41e7f860e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63de453f649fe038eb9f0a039cbfe79942843abc46c7de9e02bb4e41e7f860e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps hosted CPU saturation bounded across source-run and native artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
