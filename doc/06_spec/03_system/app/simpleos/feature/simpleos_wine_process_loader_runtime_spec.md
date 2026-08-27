# Simpleos Wine Process Loader Runtime Specification

> Tests covering SimpleOS Wine loader runtime preflight, REQ-035: full-image loader runtime evidence before arbitrary execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Loader Runtime Specification

## Scenarios

### SimpleOS Wine loader runtime preflight

### REQ-035: full-image loader runtime evidence before arbitrary execution

#### should compose image handoff, relocation, and TLS runtime checks without executing PE code
#### should require PEB/TEB VM byte-write readback before loader runtime evidence

- should require PEB/TEB VM byte-write readback before loader runtime evidence
   - Expected: result.ok is true
   - Expected: result.status equals `full-image-loader-runtime-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before loader runtime evidence")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_plan_full_image_loader_runtime_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("full-image-loader-runtime-planned")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine loader runtime preflight, REQ-035: full-image loader runtime evidence before arbitrary execution.
- SimpleOS Wine loader runtime preflight
- REQ-035: full-image loader runtime evidence before arbitrary execution

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
- `REQ-035`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `77d63819c73f1644a894c7337cb00019b8a01f4ec1800a1a9f2ffbde352a7f81`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77d63819c73f1644a894c7337cb00019b8a01f4ec1800a1a9f2ffbde352a7f81`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77d63819c73f1644a894c7337cb00019b8a01f4ec1800a1a9f2ffbde352a7f81`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=80 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl:40:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should compose image handoff, relocation, and TLS runtime checks without executing PE code' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should compose image handoff, relocation, and TLS runtime checks without executing PE code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before loader runtime evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before loader runtime evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
