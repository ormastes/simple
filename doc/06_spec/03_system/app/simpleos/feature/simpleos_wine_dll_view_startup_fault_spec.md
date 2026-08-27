# Simpleos Wine Dll View Startup Fault Specification

> Tests covering REQ-044: DLL view startup fault rollback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Startup Fault Specification

## Scenarios

### REQ-044: DLL view startup fault rollback

#### records SEH rollback around DllMain startup while keeping DLL code non-executing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-044
```

</details>

#### requires PEB/TEB write-gated DllMain handoff before startup rollback

- requires PEB/TEB write-gated DllMain handoff before startup rollback
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-startup-fault-rollback-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB write-gated DllMain handoff before startup rollback")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x502100, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_dll_record_file_view_startup_fault_with_peb_teb_writes("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", fault, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-startup-fault-rollback-recorded")
expect(result.evidence).to_contain("peb-teb-writes-ready")
expect(result.evidence).to_contain("ProcessParametersWrite")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### requires PEB/TEB layout-gated DllMain handoff before startup rollback

- requires PEB/TEB layout-gated DllMain handoff before startup rollback
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-startup-fault-rollback-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB layout-gated DllMain handoff before startup rollback")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x502100, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_dll_record_file_view_startup_fault_with_peb_teb_layout("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", fault, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", layout)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-startup-fault-rollback-recorded")
expect(result.evidence).to_contain("peb-teb-layout-ready")
expect(result.evidence).to_contain("PEBTEBLayoutWritePlan")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### requires PEB/TEB VM byte-write readback before startup rollback

- requires PEB/TEB VM byte-write readback before startup rollback
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-startup-fault-rollback-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB VM byte-write readback before startup rollback")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x502100, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val layout_bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), layout_bytes)
val result = wine_dll_record_file_view_startup_fault_with_peb_teb_vm_writes("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", fault, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-startup-fault-rollback-recorded")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-044: DLL view startup fault rollback.
- REQ-044: DLL view startup fault rollback

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
- `REQ-044`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cf3a19e9a40e242b465e6f7acb90d349083e1ef52cab99b7a2734bd0a0fee024`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf3a19e9a40e242b465e6f7acb90d349083e1ef52cab99b7a2734bd0a0fee024`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf3a19e9a40e242b465e6f7acb90d349083e1ef52cab99b7a2734bd0a0fee024`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl:116:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records SEH rollback around DllMain startup while keeping DLL code non-executing' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB write-gated DllMain handoff before startup rollback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB layout-gated DllMain handoff before startup rollback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB VM byte-write readback before startup rollback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
