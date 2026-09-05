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

- should map a validated full-Wine process image into an OS-backed VM without executing it


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-028
# @req REQ-SSPEC-SYSTEM
step("should map a validated full-Wine process image into an OS-backed VM without executing it")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val handoff = wine_process_prepare_full_image_handoff(plan, wine_known_hello_exe_fixture_bytes())
assert_equal(handoff.ok, true)
assert_equal(handoff.mapped_base, 0x400000)
assert_equal(handoff.mapped_size, 0x5000)
assert_equal(handoff.entry_address, 0x402000)
assert_contains(handoff.evidence, "arbitrary-process-image-handoff")
assert_contains(handoff.evidence, "os-vma")
assert_contains(handoff.evidence, "thread-stack")
assert_contains(handoff.evidence, "guard-page")
assert_contains(handoff.evidence, "no-host-code-jump")
assert_equal(handoff.status, "full-image-handoff-ready")
```

</details>

#### should keep arbitrary image handoff behind full-Wine and PE validation gates

- should keep arbitrary image handoff behind full-Wine and PE validation gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep arbitrary image handoff behind full-Wine and PE validation gates")
val controlled = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val unsupported = wine_process_prepare_full_image_handoff(controlled, wine_known_hello_exe_fixture_bytes())
assert_equal(unsupported.ok, false)
assert_equal(unsupported.error, "unsupported-process-session")

val full = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val malformed = wine_process_prepare_full_image_handoff(full, _zero_bytes(0))
assert_equal(malformed.ok, false)
assert_equal(malformed.error, "too-small")
```

</details>

#### should require PEB/TEB VM byte-write readback before full image handoff readiness

- should require PEB/TEB VM byte-write readback before full image handoff readiness


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

assert_equal(handoff.ok, true)
assert_equal(handoff.status, "full-image-handoff-ready")
assert_contains(handoff.evidence, "peb-teb-vm-writes-ready")
assert_contains(handoff.evidence, "VMWriteReadback:PEBTEBLayoutBytes")
assert_contains(handoff.evidence, "arbitrary-process-image-handoff")
```

</details>

#### should block full image handoff before image mapping when PEB/TEB VM byte writes fail

- should block full image handoff before image mapping when PEB/TEB VM byte writes fail


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

assert_equal(handoff.ok, false)
assert_equal(handoff.error, "peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
assert_equal(handoff.status, "rejected")
assert_equal(handoff.mapped_base, 0)
assert_equal(handoff.entry_address, 0)
assert_contains(handoff.evidence, "full-image-handoff-blocked")
assert_contains(handoff.evidence, "no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl` |
| Updated | 2026-08-27 |
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

- Canonical SPipe generation for source `ddccdbf6e12af5cb5092f34aa9db8f16a3b65e422c957d641f528d6246384a9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ddccdbf6e12af5cb5092f34aa9db8f16a3b65e422c957d641f528d6246384a9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ddccdbf6e12af5cb5092f34aa9db8f16a3b65e422c957d641f528d6246384a9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map a validated full-Wine process image into an OS-backed VM without executing it' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should map a validated full-Wine process image into an OS-backed VM without executing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep arbitrary image handoff behind full-Wine and PE validation gates' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep arbitrary image handoff behind full-Wine and PE validation gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before full image handoff readiness' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before full image handoff readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block full image handoff before image mapping when PEB/TEB VM byte writes fail' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
