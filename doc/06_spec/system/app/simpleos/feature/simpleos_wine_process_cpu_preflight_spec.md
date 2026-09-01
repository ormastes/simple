# Simpleos Wine Process Cpu Preflight Specification

> Tests covering SimpleOS Wine CPU dispatch VM preflight, REQ-017: process CPU dispatch preflight.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Cpu Preflight Specification

## Scenarios

### SimpleOS Wine CPU dispatch VM preflight

### REQ-017: process CPU dispatch preflight

#### should require PEB/TEB VM byte-write readback before CPU dispatch preflight

- should require PEB/TEB VM byte-write readback before CPU dispatch preflight
   - Expected: preflight.ok is true
   - Expected: preflight.status equals `cpu-preflight-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        # @req REQ-SSPEC-SYSTEM
        # @req REQ-017
    # @req REQ-017
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before CPU dispatch preflight")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val preflight = wine_process_cpu_dispatch_preflight_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(preflight.ok).to_equal(true)
expect(preflight.evidence).to_contain("peb-teb-vm-writes-ready")
expect(preflight.evidence).to_contain("process-image-mapped")
expect(preflight.evidence).to_contain("x86_64-dispatch")
expect(preflight.status).to_equal("cpu-preflight-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine CPU dispatch VM preflight, REQ-017: process CPU dispatch preflight.
- SimpleOS Wine CPU dispatch VM preflight
- REQ-017: process CPU dispatch preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-017`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5041aca247acf77c0b62003bd972d3a9ff2f6a9df30a054227e51bc5393930c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5041aca247acf77c0b62003bd972d3a9ff2f6a9df30a054227e51bc5393930c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5041aca247acf77c0b62003bd972d3a9ff2f6a9df30a054227e51bc5393930c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.md (current)
findings: 5 blockers: 0
  narrative=80 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before CPU dispatch preflight' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before CPU dispatch preflight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
