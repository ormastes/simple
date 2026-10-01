# Simpleos Wine Process Tls Dispatch Specification

> Tests covering SimpleOS Wine TLS callback dispatch, REQ-037: loader-owned TLS callback dispatch record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Tls Dispatch Specification

## Scenarios

### SimpleOS Wine TLS callback dispatch

### REQ-037: loader-owned TLS callback dispatch record

#### should record a mapped TLS callback dispatch after relocation without executing PE code

- should record a mapped TLS callback dispatch after relocation without executing PE code
   - Expected: result.ok is true
   - Expected: result.callback_count equals `1`
   - Expected: result.first_callback_rva equals `0x2000`
   - Expected: result.dispatch_count equals `1`
   - Expected: result.status equals `tls-callback-dispatch-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-037
# @req REQ-SSPEC-SYSTEM
step("should record a mapped TLS callback dispatch after relocation without executing PE code")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_record_tls_callback_dispatch(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.callback_count).to_equal(1)
expect(result.first_callback_rva).to_equal(0x2000)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("tls-callback-target-mapped")
expect(result.evidence).to_contain("loader-tls-callback-dispatch-owned")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("tls-callback-dispatch-recorded")
```

</details>

#### should require PEB/TEB VM byte-write readback before TLS callback dispatch record

- should require PEB/TEB VM byte-write readback before TLS callback dispatch record
   - Expected: result.ok is true
   - Expected: result.status equals `tls-callback-dispatch-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before TLS callback dispatch record")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_record_tls_callback_dispatch_with_peb_teb_vm_writes(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("tls-callback-dispatch-recorded")
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
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine TLS callback dispatch, REQ-037: loader-owned TLS callback dispatch record.
- SimpleOS Wine TLS callback dispatch
- REQ-037: loader-owned TLS callback dispatch record

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
- `REQ-037`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b53421b0338ac4c467cec3509b77866c2b46fcd79e0c92b8f313fc486b45edd6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b53421b0338ac4c467cec3509b77866c2b46fcd79e0c92b8f313fc486b45edd6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b53421b0338ac4c467cec3509b77866c2b46fcd79e0c92b8f313fc486b45edd6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record a mapped TLS callback dispatch after relocation without executing PE code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should record a mapped TLS callback dispatch after relocation without executing PE code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before TLS callback dispatch record' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before TLS callback dispatch record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
