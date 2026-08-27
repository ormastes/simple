# Multicore Green Explicit Sliced Fairness Regression

> This SSpec proves the explicit Pure Simple sliced-task API can provide a hosted fairness contract without claiming automatic preemption for ordinary `multicore_green_spawn` closures. With hosted parallelism pinned to `1`, a long sliced task requeues itself between short slices, allowing a later quick task to complete during the first observation window on both source-run and standalone native paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Explicit Sliced Fairness Regression

This SSpec proves the explicit Pure Simple sliced-task API can provide a hosted fairness contract without claiming automatic preemption for ordinary `multicore_green_spawn` closures. With hosted parallelism pinned to `1`, a long sliced task requeues itself between short slices, allowing a later quick task to complete during the first observation window on both source-run and standalone native paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-sliced-fairness |
| Category | Runtime / Hosted / Multicore Green |
| Status | Regression |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md |
| Source | `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec proves the explicit Pure Simple sliced-task API can provide a
hosted fairness contract without claiming automatic preemption for ordinary
`multicore_green_spawn` closures. With hosted parallelism pinned to `1`, a
long sliced task requeues itself between short slices, allowing a later quick
task to complete during the first observation window on both source-run and
standalone native paths.

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
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### multicore green explicit sliced fairness

#### lets a quick task run between explicit slices without growing hosted parallelism

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lets a quick task run between explicit slices without growing hosted parallelism
- Prepare the native output directory for the sliced fairness fixture
   - Expected: mkdir_code equals `0`
- The fixture type-checks with the public sliced API
   - Expected: check_code equals `0`
- Compile the fixture to standalone native
   - Expected: native_compile_code equals `0`
- Run the fixture through the hosted source path
   - Expected: interp_code equals `0`
- Run the fixture through the hosted standalone native path
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lets a quick task run between explicit slices without growing hosted parallelism")
step("Prepare the native output directory for the sliced fairness fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)

step("The fixture type-checks with the public sliced API")
val (check_out, check_code) = shell(SIMPLE_BIN + " check " + SOURCE_PATH)
expect(check_code).to_equal(0)
expect(check_out).to_contain("All checks passed")

step("Compile the fixture to standalone native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture through the hosted source path")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect_sliced_fairness_output(interp_out)
expect(interp_code).to_equal(0)

step("Run the fixture through the hosted standalone native path")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect_sliced_fairness_output(native_out)
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

- Canonical SPipe generation for source `4f75baaa9d78980bfaf22605bae3f6c85bac0658eff82d1813c1c18597362285`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f75baaa9d78980bfaf22605bae3f6c85bac0658eff82d1813c1c18597362285`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f75baaa9d78980bfaf22605bae3f6c85bac0658eff82d1813c1c18597362285`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets a quick task run between explicit slices without growing hosted parallelism' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
