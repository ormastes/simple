# Wine Process Session Module Loader Specification

> Tests covering Wine process session module loader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Module Loader Specification

## Scenarios

### Wine process session module loader

#### resolves a bounded KERNEL32 module procedure for full Wine plans

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a bounded KERNEL32 module procedure for full Wine plans
   - Expected: result.ok is true
   - Expected: result.command equals `game.exe`
   - Expected: result.module_name equals `kernel32.dll`
   - Expected: result.proc_name equals `GetProcAddress`
   - Expected: result.handle equals `0x120`
   - Expected: result.proc_address equals `0x120000 + 3`
   - Expected: result.operations equals `GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary`
   - Expected: result.status equals `module-resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a bounded KERNEL32 module procedure for full Wine plans")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_known_kernel32_module(plan, "kernel32.dll", "GetProcAddress")
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.module_name).to_equal("kernel32.dll")
expect(result.proc_name).to_equal("GetProcAddress")
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(result.status).to_equal("module-resolved")
```

</details>

#### resolves a bounded KERNEL32 module procedure through LoadLibraryExW

- resolves a bounded KERNEL32 module procedure through LoadLibraryExW
   - Expected: result.ok is true
   - Expected: result.command equals `game.exe`
   - Expected: result.handle equals `0x120`
   - Expected: result.proc_address equals `0x120000 + 3`
   - Expected: result.operations equals `GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary`
   - Expected: result.status equals `module-resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a bounded KERNEL32 module procedure through LoadLibraryExW")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 0)
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(result.status).to_equal("module-resolved")
```

</details>

#### rejects unsupported modules and non-full-Wine sessions

- rejects unsupported modules and non-full-Wine sessions
   - Expected: missing.ok is false
   - Expected: missing.error equals `GetModuleHandleW:module-not-loaded`
   - Expected: missing.status equals `rejected`
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `unsupported-process-session`
   - Expected: blocked.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported modules and non-full-Wine sessions")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val missing = wine_process_resolve_known_kernel32_module(plan, "user32.dll", "MessageBoxW")
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("GetModuleHandleW:module-not-loaded")
expect(missing.status).to_equal("rejected")

val hello = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\Games"), _hello_gates())
val blocked = wine_process_resolve_known_kernel32_module(hello, "kernel32.dll", "GetProcAddress")
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("unsupported-process-session")
expect(blocked.status).to_equal("blocked")
```

</details>

#### rejects unsupported LoadLibraryExW flags

- rejects unsupported LoadLibraryExW flags
   - Expected: result.ok is false
   - Expected: result.error equals `LoadLibraryExW:unsupported-load-flags`
   - Expected: result.operations equals `GetModuleHandleW`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported LoadLibraryExW flags")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("LoadLibraryExW:unsupported-load-flags")
expect(result.operations).to_equal("GetModuleHandleW")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_module_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session module loader.
- Wine process session module loader

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7f71832f68c870db5ba1d4f6e48a0bf9547654308b4e3eed486cc3815724d07f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f71832f68c870db5ba1d4f6e48a0bf9547654308b4e3eed486cc3815724d07f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f71832f68c870db5ba1d4f6e48a0bf9547654308b4e3eed486cc3815724d07f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/wine_process_session_module_loader_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_module_loader_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_module_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_module_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_module_loader_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a bounded KERNEL32 module procedure for full Wine plans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_module_loader_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a bounded KERNEL32 module procedure through LoadLibraryExW' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_module_loader_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported modules and non-full-Wine sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
