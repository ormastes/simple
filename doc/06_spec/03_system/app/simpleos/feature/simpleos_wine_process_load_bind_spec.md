# Simpleos Wine Process Load Bind Specification

> Tests covering SimpleOS Wine process load and bind, REQ-022: load then bind known KERNEL32 imports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Load Bind Specification

## Scenarios

### SimpleOS Wine process load and bind

### REQ-022: load then bind known KERNEL32 imports

#### resolve the first import module before accepting known import bindings

- resolve the first import module before accepting known import bindings
   - Expected: result.ok is true
   - Expected: result.dll_name equals `kernel32.dll`
   - Expected: result.module_handle equals `0x120`
   - Expected: result.call_sequence equals `GetStdHandle WriteFile ExitProcess`
   - Expected: result.binding_count equals `3`
   - Expected: result.status equals `imports-loaded-bound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-022
# @req REQ-SSPEC-SYSTEM
step("resolve the first import module before accepting known import bindings")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_load_and_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.module_handle).to_equal(0x120)  # oracle: result.module_handle must equal 0x120 — authoritative contract constant
expect(result.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(result.binding_count).to_equal(3)  # oracle: result.binding_count must equal 3 — authoritative contract constant
expect(result.status).to_equal("imports-loaded-bound")
```

</details>

#### reject load-and-bind before module resolution passes

- reject load-and-bind before module resolution passes
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject load-and-bind before module resolution passes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_load_and_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_load_bind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine process load and bind, REQ-022: load then bind known KERNEL32 imports.
- SimpleOS Wine process load and bind
- REQ-022: load then bind known KERNEL32 imports

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
- `REQ-022`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2e0e5c966668857c4a78120254d1e72294ece5dfc29d66820d83b95a8fe8ea6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2e0e5c966668857c4a78120254d1e72294ece5dfc29d66820d83b95a8fe8ea6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2e0e5c966668857c4a78120254d1e72294ece5dfc29d66820d83b95a8fe8ea6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_load_bind_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_load_bind_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_load_bind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_load_bind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
