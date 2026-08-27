# Cooperative Green SMF Function-Global Regression

> This SSpec keeps SMF function-valued global storage covered after the runtime fix that restored `__module_init` execution before SMF entry calls. Minimal SMF fixtures with a function-valued global slot or a global function-valued array must both compile and run successfully.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green SMF Function-Global Regression

This SSpec keeps SMF function-valued global storage covered after the runtime fix that restored `__module_init` execution before SMF entry calls. Minimal SMF fixtures with a function-valued global slot or a global function-valued array must both compile and run successfully.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-smf-function-global |
| Category | Runtime / SMF / Concurrency |
| Status | Regression Coverage |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps SMF function-valued global storage covered after the runtime
fix that restored `__module_init` execution before SMF entry calls. Minimal SMF
fixtures with a function-valued global slot or a global function-valued array
must both compile and run successfully.

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
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl --mode=interpreter --clean
```

## Examples

- The function-valued global-slot fixture must compile to SMF and print its pass marker.
- The global function-array fixture must compile to SMF and print its pass marker.
- The regression closes the historical crash path where SMF skipped `__module_init`
  before entering `spl_main`.

## Scenarios

### Cooperative green SMF function-global regression

#### runs SMF function-valued globals and global arrays after module init

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs SMF function-valued globals and global arrays after module init
- Write the minimal function-valued SMF fixtures
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(FUNCTION_GLOBAL_SOURCE, function_global_fixture_source()) is true
   - Expected: rt_file_write_text(GLOBAL_ARRAY_SOURCE, global_function_array_fixture_source()) is true
- Compile the function-valued global-slot fixture to SMF
   - Expected: compile_global_code equals `0`
- Compile the global function-array fixture to SMF
   - Expected: compile_array_code equals `0`
- Run the function-valued global-slot SMF and verify the pass marker
   - Expected: run_global_code equals `0`
- Run the global function-array SMF and verify the pass marker
   - Expected: run_array_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs SMF function-valued globals and global arrays after module init")
step("Write the minimal function-valued SMF fixtures")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(FUNCTION_GLOBAL_SOURCE, function_global_fixture_source())).to_equal(true)
expect(rt_file_write_text(GLOBAL_ARRAY_SOURCE, global_function_array_fixture_source())).to_equal(true)

step("Compile the function-valued global-slot fixture to SMF")
val (compile_global_out, compile_global_code) = shell(SIMPLE_BIN + " compile " + FUNCTION_GLOBAL_SOURCE + " -o " + FUNCTION_GLOBAL_SMF)
expect(compile_global_out).to_contain("Compiled")
expect(compile_global_code).to_equal(0)

step("Compile the global function-array fixture to SMF")
val (compile_array_out, compile_array_code) = shell(SIMPLE_BIN + " compile " + GLOBAL_ARRAY_SOURCE + " -o " + GLOBAL_ARRAY_SMF)
expect(compile_array_out).to_contain("Compiled")
expect(compile_array_code).to_equal(0)

step("Run the function-valued global-slot SMF and verify the pass marker")
val (run_global_out, run_global_code) = shell("timeout 20s " + SIMPLE_BIN + " " + FUNCTION_GLOBAL_SMF)
expect(run_global_out).to_contain("function_global_smf_pass=true")
expect(run_global_code).to_equal(0)

step("Run the global function-array SMF and verify the pass marker")
val (run_array_out, run_array_code) = shell("timeout 20s " + SIMPLE_BIN + " " + GLOBAL_ARRAY_SMF)
expect(run_array_out).to_contain("global_function_array_smf_pass=true")
expect(run_array_code).to_equal(0)
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

- Canonical SPipe generation for source `4d8b26e8597feefb8859a801ebbd9bed90c1887a043095e8ec7dcf6fa11251bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d8b26e8597feefb8859a801ebbd9bed90c1887a043095e8ec7dcf6fa11251bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d8b26e8597feefb8859a801ebbd9bed90c1887a043095e8ec7dcf6fa11251bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs SMF function-valued globals and global arrays after module init' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
