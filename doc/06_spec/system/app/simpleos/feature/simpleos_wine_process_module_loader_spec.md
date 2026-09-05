# Simpleos Wine Process Module Loader Specification

> Tests covering SimpleOS Wine process module loader, REQ-020: bounded process module resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Module Loader Specification

## Scenarios

### SimpleOS Wine process module loader

### REQ-020: bounded process module resolution

#### should resolve a known KERNEL32 module procedure for a full-Wine process plan

- should resolve a known KERNEL32 module procedure for a full-Wine process plan
   - Expected: resolution.ok is true
   - Expected: resolution.handle equals `0x120`
   - Expected: resolution.proc_address equals `0x120000 + 3`
   - Expected: resolution.operations equals `GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary`
   - Expected: resolution.status equals `module-resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-020
# @req REQ-SSPEC-SYSTEM
step("should resolve a known KERNEL32 module procedure for a full-Wine process plan")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_known_kernel32_module(plan, "kernel32.dll", "GetProcAddress")
expect(resolution.ok).to_equal(true)
expect(resolution.handle).to_equal(0x120)
expect(resolution.proc_address).to_equal(0x120000 + 3)
expect(resolution.operations).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(resolution.status).to_equal("module-resolved")
```

</details>

#### should resolve a known KERNEL32 module procedure through LoadLibraryExW

- should resolve a known KERNEL32 module procedure through LoadLibraryExW
   - Expected: resolution.ok is true
   - Expected: resolution.handle equals `0x120`
   - Expected: resolution.proc_address equals `0x120000 + 3`
   - Expected: resolution.operations equals `GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary`
   - Expected: resolution.status equals `module-resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve a known KERNEL32 module procedure through LoadLibraryExW")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 0)
expect(resolution.ok).to_equal(true)
expect(resolution.handle).to_equal(0x120)
expect(resolution.proc_address).to_equal(0x120000 + 3)
expect(resolution.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(resolution.status).to_equal("module-resolved")
```

</details>

#### should block module resolution outside the full-Wine process-session gate

- should block module resolution outside the full-Wine process-session gate
   - Expected: resolution.ok is false
   - Expected: resolution.error equals `unsupported-process-session`
   - Expected: resolution.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block module resolution outside the full-Wine process-session gate")
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\Games"), _hello_gates())
val resolution = wine_process_resolve_known_kernel32_module(plan, "kernel32.dll", "GetProcAddress")
expect(resolution.ok).to_equal(false)
expect(resolution.error).to_equal("unsupported-process-session")
expect(resolution.status).to_equal("blocked")
```

</details>

#### should reject unsupported LoadLibraryExW flags

- should reject unsupported LoadLibraryExW flags
   - Expected: resolution.ok is false
   - Expected: resolution.error equals `LoadLibraryExW:unsupported-load-flags`
   - Expected: resolution.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unsupported LoadLibraryExW flags")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 8)
expect(resolution.ok).to_equal(false)
expect(resolution.error).to_equal("LoadLibraryExW:unsupported-load-flags")
expect(resolution.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine process module loader, REQ-020: bounded process module resolution.
- SimpleOS Wine process module loader
- REQ-020: bounded process module resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-020`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd969facc5356ceef388b8515b465510eb67e516c69b6a5ba7b780b2772c9f22`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd969facc5356ceef388b8515b465510eb67e516c69b6a5ba7b780b2772c9f22`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd969facc5356ceef388b8515b465510eb67e516c69b6a5ba7b780b2772c9f22`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve a known KERNEL32 module procedure for a full-Wine process plan' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve a known KERNEL32 module procedure for a full-Wine process plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve a known KERNEL32 module procedure through LoadLibraryExW' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve a known KERNEL32 module procedure through LoadLibraryExW' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block module resolution outside the full-Wine process-session gate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should block module resolution outside the full-Wine process-session gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported LoadLibraryExW flags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
