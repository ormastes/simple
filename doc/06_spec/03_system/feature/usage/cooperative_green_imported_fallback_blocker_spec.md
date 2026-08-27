# Cooperative Green Imported Fallback Native Regression

> This SSpec keeps the imported cooperative-green value helper fixed across the interpreter, SMF, and standalone native paths. A minimal value-only workload that calls `cooperative_green_spawn_value(...)` from an imported stdlib module must compile and run successfully on all three paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Imported Fallback Native Regression

This SSpec keeps the imported cooperative-green value helper fixed across the interpreter, SMF, and standalone native paths. A minimal value-only workload that calls `cooperative_green_spawn_value(...)` from an imported stdlib module must compile and run successfully on all three paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-cooperative-imported-fallback-native |
| Category | Runtime / Native / Interpreter Fallback |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Research | doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md |
| Source | `test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the imported cooperative-green value helper fixed across the
interpreter, SMF, and standalone native paths. A minimal value-only workload
that calls `cooperative_green_spawn_value(...)` from an imported stdlib module
must compile and run successfully on all three paths.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md

## Syntax

```sh
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl --mode=interpreter --clean
```

## Scenarios

### cooperative green imported fallback native regression

#### keeps imported cooperative_green_spawn_value working across interpreter, SMF, and native

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps imported cooperative_green_spawn_value working across interpreter, SMF, and native
- Write the minimal imported cooperative-green value-only fixture
   - Expected: mkdir_code equals `0`
   - Expected: rt_file_write_text(SOURCE_PATH, fixture_source()) is true
- Compile the fixture to SMF
   - Expected: smf_compile_code equals `0`
- Compile the fixture to native
   - Expected: native_compile_code equals `0`
- Run the fixture in the interpreter as the control
   - Expected: interp_code equals `0`
- Keep the fixed imported-function SMF path green
   - Expected: smf_code equals `0`
- Keep the standalone native path green
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps imported cooperative_green_spawn_value working across interpreter, SMF, and native")
step("Write the minimal imported cooperative-green value-only fixture")
val (mkdir_out, mkdir_code) = shell("mkdir -p " + BUILD_DIR)
expect(mkdir_out.len()).to_be_greater_than(-1)
expect(mkdir_code).to_equal(0)
expect(rt_file_write_text(SOURCE_PATH, fixture_source())).to_equal(true)

step("Compile the fixture to SMF")
val (smf_compile_out, smf_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " -o " + SMF_PATH)
expect(smf_compile_out).to_contain("Compiled")
expect(smf_compile_code).to_equal(0)

step("Compile the fixture to native")
val (native_compile_out, native_compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(native_compile_out).to_contain("Compiled")
expect(native_compile_code).to_equal(0)

step("Run the fixture in the interpreter as the control")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(interp_out).to_contain("cooperative_green_spawn_value_literal_pass=true")
expect(interp_code).to_equal(0)

step("Keep the fixed imported-function SMF path green")
val (smf_out, smf_code) = shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)
expect(smf_out).to_contain("cooperative_green_spawn_value_literal_pass=true")
expect(smf_code).to_equal(0)

step("Keep the standalone native path green")
val (native_out, native_code) = shell("timeout 20s " + NATIVE_PATH)
expect(native_out).to_contain("cooperative_green_spawn_value_literal_pass=true")
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
- **Research:** `doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af28ee81eaa49ad114eb12d15d5f0c125ea101a0645472b13e85580dfe15b30f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af28ee81eaa49ad114eb12d15d5f0c125ea101a0645472b13e85580dfe15b30f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af28ee81eaa49ad114eb12d15d5f0c125ea101a0645472b13e85580dfe15b30f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cooperative_green_imported_fallback_blocker_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps imported cooperative_green_spawn_value working across interpreter, SMF, and native' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
