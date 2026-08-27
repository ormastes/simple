# Cooperative Green Spec Runner Regression

> This SSpec guards the interpreter-mode runner contract for green/cooperative queue APIs. The same minimal green-thread queue logic must pass under both `simple run` and `simple test`, so later runner/cache changes cannot re-open the earlier mismatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Spec Runner Regression

This SSpec guards the interpreter-mode runner contract for green/cooperative queue APIs. The same minimal green-thread queue logic must pass under both `simple run` and `simple test`, so later runner/cache changes cannot re-open the earlier mismatch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-spec-runner-regression |
| Category | Test Runner / Cooperative Green |
| Status | Regression Coverage |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md |
| Source | `test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec guards the interpreter-mode runner contract for green/cooperative
queue APIs. The same minimal green-thread queue logic must pass under both
`simple run` and `simple test`, so later runner/cache changes cannot re-open
the earlier mismatch.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md

## Syntax

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl --mode=interpreter --clean
```

## Scenarios

### cooperative green spec runner regression

#### keeps direct value scheduling aligned between simple run and simple test

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps direct value scheduling aligned between simple run and simple test
- Write the direct-run and SSpec probe fixtures
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(RUN_PATH, run_probe_source()) is true
   - Expected: rt_file_write_text(SPEC_PATH, spec_probe_source()) is true
- Verify the green-thread probe passes under simple run
   - Expected: run_code equals `0`
- Verify the same green-thread probe also passes under simple test
   - Expected: test_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps direct value scheduling aligned between simple run and simple test")
step("Write the direct-run and SSpec probe fixtures")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(RUN_PATH, run_probe_source())).to_equal(true)
expect(rt_file_write_text(SPEC_PATH, spec_probe_source())).to_equal(true)

step("Verify the green-thread probe passes under simple run")
val (run_out, run_code) = shell(SIMPLE_BIN + " run " + RUN_PATH)
expect(run_out).to_contain("green_run_probe_pass=true")
expect(run_code).to_equal(0)

step("Verify the same green-thread probe also passes under simple test")
val (test_out, test_code) = shell(SIMPLE_BIN + " test " + SPEC_PATH + " --mode=interpreter --clean")
expect(test_out).to_contain("PASSED")
expect(test_out).to_contain("green_probe_spec")
expect(test_code).to_equal(0)
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
- **Research:** `doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `abeb46e69dc4fc9b255223acffb99f729f16e379a56278b4cd5d9f51bfe71d3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abeb46e69dc4fc9b255223acffb99f729f16e379a56278b4cd5d9f51bfe71d3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abeb46e69dc4fc9b255223acffb99f729f16e379a56278b4cd5d9f51bfe71d3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps direct value scheduling aligned between simple run and simple test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
