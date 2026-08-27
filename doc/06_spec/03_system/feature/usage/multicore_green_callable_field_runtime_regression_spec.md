# Multicore Green Callable Field Runtime Regression

> This SSpec covers the fixed callable-field runtime boundary underneath the broader multicore-green sliced fairness experiment: a zero-argument function-valued object field backed by captured mutable state now works on both source-run and standalone native.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Callable Field Runtime Regression

This SSpec covers the fixed callable-field runtime boundary underneath the broader multicore-green sliced fairness experiment: a zero-argument function-valued object field backed by captured mutable state now works on both source-run and standalone native.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #multicore-green-callable-field-runtime |
| Category | Runtime / Native / Concurrency |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec covers the fixed callable-field runtime boundary underneath the
broader multicore-green sliced fairness experiment: a zero-argument
function-valued object field backed by captured mutable state now works on both
source-run and standalone native.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the regression contract:

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl --mode=interpreter --clean
```

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl
multicore green callable field runtime regression PASSED
Files: 1
Passed: 1
Failed: 0
```

## Traceability Expectations

- The probe stores a zero-argument function in an object field.
- The stored callable captures mutable local state through a holder.
- Source-run evidence must print `a=41` and `b=42`.
- Standalone native evidence must print the same values.
- Standalone native evidence must include `EXIT=0`.
- The tracker must keep the callable-field blocker marked fixed.
- The tracker must describe this callable-field boundary as closed, not pending.
- The test command must honor `SIMPLE_BIN` for Docker-isolated runs.
- The Syntax block must not point at the stale `bin/release/simple` wrapper.
- This regression protects function-value runtime behavior used by the M:N lane.
- It is not a substitute for runtime-pool `used_runtime_pool()` profile evidence.
- It is not cooperative-green CPU-parallel evidence.
- The generated manual must keep source-run and native parity visible.

## Scenarios

### Multicore green callable field runtime regression

#### keeps the escaped callable-field closure path working

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the escaped callable-field closure path working
- Write the hosted callable-field probe
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Source-run keeps the expected captured-thunk values
   - Expected: run_code equals `0`
- Standalone native keeps the same escaped captured-callable shape working
   - Expected: compile_code equals `0`
   - Expected: native_code equals `0`
- The tracking note records the fixed callable-field boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the escaped callable-field closure path working")
step("Write the hosted callable-field probe")
val (_mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, fixture_source())).to_equal(true)

step("Source-run keeps the expected captured-thunk values")
val (run_out, run_code) = shell(simple_bin() + " run " + SOURCE_PATH)
expect(run_code).to_equal(0)
expect(run_out).to_contain("a=41")
expect(run_out).to_contain("b=42")

step("Standalone native keeps the same escaped captured-callable shape working")
val (compile_out, compile_code) = shell(simple_bin() + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/mcg_callable_field.out 2>&1; code=$?; cat /tmp/mcg_callable_field.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("a=41")
expect(native_out).to_contain("b=42")
expect(native_out).to_contain("EXIT=0")

step("The tracking note records the fixed callable-field boundary")
val blocker = read_text("doc/08_tracking/bug/multicore_green_callable_field_runtime_blocker_2026-06-11.md")
expect(blocker).to_contain("Status: fixed")
expect(blocker).to_contain("fresh native compiler/runtime now runs the same probe successfully")
expect(blocker).to_contain("Because this boundary is closed")
expect(blocker).to_contain("The broader hosted fairness/preemption gap remains tracked separately.")
expect(blocker).to_contain("a=41")
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
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1fa7ba810a62c866215f39ca2c7c7ce83fac7b8faca3ab4531caab613979386d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1fa7ba810a62c866215f39ca2c7c7ce83fac7b8faca3ab4531caab613979386d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1fa7ba810a62c866215f39ca2c7c7ce83fac7b8faca3ab4531caab613979386d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/multicore_green_callable_field_runtime_regression_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the escaped callable-field closure path working' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
