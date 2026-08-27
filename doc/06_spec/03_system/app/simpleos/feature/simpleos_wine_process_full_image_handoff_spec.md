# Simpleos Wine Process Full Image Handoff Specification

> Tests covering SimpleOS Wine full image handoff, REQ-028: arbitrary process image VM handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Full Image Handoff Specification

## Scenarios

### SimpleOS Wine full image handoff

### REQ-028: arbitrary process image VM handoff

#### should map a validated full-Wine process image into an OS-backed VM without executing it
#### should keep arbitrary image handoff behind full-Wine and PE validation gates

- should keep arbitrary image handoff behind full-Wine and PE validation gates
   - Expected: unsupported.ok is false
   - Expected: unsupported.error equals `unsupported-process-session`
   - Expected: malformed.ok is false
   - Expected: malformed.error equals `too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep arbitrary image handoff behind full-Wine and PE validation gates")
val controlled = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val unsupported = wine_process_prepare_full_image_handoff(controlled, wine_known_hello_exe_fixture_bytes())
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("unsupported-process-session")

val full = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val malformed = wine_process_prepare_full_image_handoff(full, _zero_bytes(0))
expect(malformed.ok).to_equal(false)
expect(malformed.error).to_equal("too-small")
```

</details>

#### should require PEB/TEB VM byte-write readback before full image handoff readiness

- should require PEB/TEB VM byte-write readback before full image handoff readiness
   - Expected: handoff.ok is true
   - Expected: handoff.status equals `full-image-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before full image handoff readiness")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val handoff = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("full-image-handoff-ready")
expect(handoff.evidence).to_contain("peb-teb-vm-writes-ready")
expect(handoff.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(handoff.evidence).to_contain("arbitrary-process-image-handoff")
```

</details>

#### should block full image handoff before image mapping when PEB/TEB VM byte writes fail

- should block full image handoff before image mapping when PEB/TEB VM byte writes fail
   - Expected: handoff.ok is false
   - Expected: handoff.error equals `peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped`
   - Expected: handoff.status equals `rejected`
   - Expected: handoff.mapped_base equals `0`
   - Expected: handoff.entry_address equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block full image handoff before image mapping when PEB/TEB VM byte writes fail")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val handoff = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(handoff.ok).to_equal(false)
expect(handoff.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(handoff.status).to_equal("rejected")
expect(handoff.mapped_base).to_equal(0)
expect(handoff.entry_address).to_equal(0)
expect(handoff.evidence).to_contain("full-image-handoff-blocked")
expect(handoff.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine full image handoff, REQ-028: arbitrary process image VM handoff.
- SimpleOS Wine full image handoff
- REQ-028: arbitrary process image VM handoff

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
- `REQ-028`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e62fe0e89a150a37915b279176a10836b8cb8b759f3abfefef485ca029acae27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e62fe0e89a150a37915b279176a10836b8cb8b759f3abfefef485ca029acae27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e62fe0e89a150a37915b279176a10836b8cb8b759f3abfefef485ca029acae27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:52:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should map a validated full-Wine process image into an OS-backed VM without executing it' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map a validated full-Wine process image into an OS-backed VM without executing it' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep arbitrary image handoff behind full-Wine and PE validation gates' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep arbitrary image handoff behind full-Wine and PE validation gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before full image handoff readiness' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before full image handoff readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block full image handoff before image mapping when PEB/TEB VM byte writes fail' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should block full image handoff before image mapping when PEB/TEB VM byte writes fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
