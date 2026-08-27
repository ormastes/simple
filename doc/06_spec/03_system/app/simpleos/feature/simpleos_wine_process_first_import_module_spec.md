# Simpleos Wine Process First Import Module Specification

> Tests covering SimpleOS Wine first-import module resolution, REQ-021: first-import module loader bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process First Import Module Specification

## Scenarios

### SimpleOS Wine first-import module resolution

### REQ-021: first-import module loader bridge

#### resolve a requested procedure against a validated first import module

- resolve a requested procedure against a validated first import module
   - Expected: resolution.ok is true
   - Expected: resolution.module_name equals `KERNEL32.dll`
   - Expected: resolution.proc_name equals `GetProcAddress`
   - Expected: resolution.operations equals `GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary`
   - Expected: resolution.status equals `module-resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-021
# @req REQ-SSPEC-SYSTEM
step("resolve a requested procedure against a validated first import module")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_first_import_module(plan, wine_known_hello_exe_fixture_bytes(), 8, "GetProcAddress")
expect(resolution.ok).to_equal(true)
expect(resolution.module_name).to_equal("KERNEL32.dll")
expect(resolution.proc_name).to_equal("GetProcAddress")
expect(resolution.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(resolution.status).to_equal("module-resolved")
```

</details>

#### reject first-import module resolution before import inspection passes

- reject first-import module resolution before import inspection passes
   - Expected: resolution.ok is false
   - Expected: resolution.error equals `invalid-symbol-limit`
   - Expected: resolution.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject first-import module resolution before import inspection passes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_first_import_module(plan, wine_known_hello_exe_fixture_bytes(), 0, "GetProcAddress")
expect(resolution.ok).to_equal(false)
expect(resolution.error).to_equal("invalid-symbol-limit")
expect(resolution.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine first-import module resolution, REQ-021: first-import module loader bridge.
- SimpleOS Wine first-import module resolution
- REQ-021: first-import module loader bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `256607e4cfd609b665b6d269e26672755c16d62d82c31b3baeb2afc957d0bc22`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `256607e4cfd609b665b6d269e26672755c16d62d82c31b3baeb2afc957d0bc22`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `256607e4cfd609b665b6d269e26672755c16d62d82c31b3baeb2afc957d0bc22`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
