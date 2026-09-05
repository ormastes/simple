# Wine Process Session Full Image Handoff Specification

> Tests covering Wine process session full image handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Full Image Handoff Specification

## Scenarios

### Wine process session full image handoff

#### maps a validated full-Wine PE image and stack into an OS-backed process VM

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps a validated full-Wine PE image and stack into an OS-backed process VM
   - Expected: result.ok is true
   - Expected: result.command equals `game.exe`
   - Expected: result.mapped_base equals `0x400000`
   - Expected: result.mapped_size equals `0x5000`
   - Expected: result.entry_address equals `0x402000`
   - Expected: result.status equals `full-image-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps a validated full-Wine PE image and stack into an OS-backed process VM")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_full_image_handoff(plan, wine_known_hello_exe_fixture_bytes())
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.mapped_base).to_equal(0x400000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.entry_address).to_equal(0x402000)
expect(result.evidence).to_contain("full-image-validated")
expect(result.evidence).to_contain("arbitrary-process-image-handoff")
expect(result.evidence).to_contain("os-process")
expect(result.evidence).to_contain("os-address-space")
expect(result.evidence).to_contain("os-vma")
expect(result.evidence).to_contain("image-map")
expect(result.evidence).to_contain("thread-stack")
expect(result.evidence).to_contain("guard-page")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("full-image-handoff-ready")
```

</details>

#### keeps full-image handoff behind full-Wine plan and image validation gates

- keeps full-image handoff behind full-Wine plan and image validation gates
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `unsupported-process-session`
   - Expected: blocked.status equals `blocked`
   - Expected: malformed.ok is false
   - Expected: malformed.error equals `too-small`
   - Expected: malformed.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps full-image handoff behind full-Wine plan and image validation gates")
val controlled = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val blocked = wine_process_prepare_full_image_handoff(controlled, wine_known_hello_exe_fixture_bytes())
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("unsupported-process-session")
expect(blocked.status).to_equal("blocked")

val full = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val malformed = wine_process_prepare_full_image_handoff(full, _zero_bytes(0))
expect(malformed.ok).to_equal(false)
expect(malformed.error).to_equal("too-small")
expect(malformed.status).to_equal("rejected")
```

</details>

#### requires PEB/TEB VM byte-write readback before full image handoff readiness

- requires PEB/TEB VM byte-write readback before full image handoff readiness
   - Expected: result.ok is true
   - Expected: result.status equals `full-image-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires PEB/TEB VM byte-write readback before full image handoff readiness")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("full-image-handoff-ready")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("arbitrary-process-image-handoff")
```

</details>

#### blocks full image handoff readiness when PEB/TEB VM byte writes are not ready

- blocks full image handoff readiness when PEB/TEB VM byte writes are not ready
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped`
   - Expected: result.status equals `rejected`
   - Expected: result.mapped_base equals `0`
   - Expected: result.entry_address equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks full image handoff readiness when PEB/TEB VM byte writes are not ready")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
expect(result.mapped_base).to_equal(0)
expect(result.entry_address).to_equal(0)
expect(result.evidence).to_contain("full-image-handoff-blocked")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session full image handoff.
- Wine process session full image handoff

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7352b924644ce76c2b7ca351d6570b2e25956e4e3554dddd43f07e2e576d1c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7352b924644ce76c2b7ca351d6570b2e25956e4e3554dddd43f07e2e576d1c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7352b924644ce76c2b7ca351d6570b2e25956e4e3554dddd43f07e2e576d1c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_full_image_handoff_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_full_image_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_full_image_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps a validated full-Wine PE image and stack into an OS-backed process VM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps full-image handoff behind full-Wine plan and image validation gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB VM byte-write readback before full image handoff readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
