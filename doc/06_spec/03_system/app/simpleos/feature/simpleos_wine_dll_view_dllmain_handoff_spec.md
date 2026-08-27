# Simpleos Wine Dll View Dllmain Handoff Specification

> Tests covering REQ-051 SimpleOS Wine DLL view DllMain handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Dllmain Handoff Specification

## Scenarios

### REQ-051 SimpleOS Wine DLL view DllMain handoff

#### prepares DllMain handoff after TLS ordering without executing DllMain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-051
```

</details>

#### requires PEB/TEB loader-lock readiness before the retained DllMain handoff

- requires PEB/TEB loader-lock readiness before the retained DllMain handoff
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB loader-lock readiness before the retained DllMain handoff")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val result = wine_dllmain_handoff_require_peb_teb_loader_lock(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock")

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-loader-lock-ready")
expect(result.evidence).to_contain("dllmain-process-attach-planned")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### requires PEB/TEB memory writes before the retained DllMain handoff

- requires PEB/TEB memory writes before the retained DllMain handoff
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB memory writes before the retained DllMain handoff")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_dllmain_handoff_require_peb_teb_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-writes-ready")
expect(result.evidence).to_contain("ProcessParametersWrite")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### requires PEB/TEB layout records before the retained DllMain handoff

- requires PEB/TEB layout records before the retained DllMain handoff
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB layout records before the retained DllMain handoff")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_dllmain_handoff_require_peb_teb_layout(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", layout)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-layout-ready")
expect(result.evidence).to_contain("PEBTEBLayoutWritePlan")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### requires PEB/TEB VM byte-write readback before the retained DllMain handoff

- requires PEB/TEB VM byte-write readback before the retained DllMain handoff
   - Expected: result.ok is true
   - Expected: result.status equals `dllmain-handoff-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB VM byte-write readback before the retained DllMain handoff")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dllmain_handoff_require_peb_teb_vm_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("PEBTEBLayoutVMReadback")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### blocks retained DllMain handoff without carrying mapped state when PEB/TEB VM byte writes fail

- blocks retained DllMain handoff without carrying mapped state when PEB/TEB VM byte writes fail
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped`
   - Expected: result.mapped_base equals `0`
   - Expected: result.mapped_size equals `0`
   - Expected: result.entrypoint_address equals `0`
   - Expected: result.callback_count equals `0`
   - Expected: result.dispatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks retained DllMain handoff without carrying mapped state when PEB/TEB VM byte writes fail")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dllmain_handoff_require_peb_teb_vm_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped")
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.entrypoint_address).to_equal(0)
expect(result.callback_count).to_equal(0)
expect(result.dispatch_count).to_equal(0)
expect(result.evidence).to_contain("dllmain-handoff-blocked")
expect(result.evidence).to_contain("no-dllmain-executed")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-051 SimpleOS Wine DLL view DllMain handoff.
- REQ-051 SimpleOS Wine DLL view DllMain handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-051`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6dfba3acc10360d7c875ac5a3c6677dfcee2e06a2ea86ba3ea44b29254eff083`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dfba3acc10360d7c875ac5a3c6677dfcee2e06a2ea86ba3ea44b29254eff083`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dfba3acc10360d7c875ac5a3c6677dfcee2e06a2ea86ba3ea44b29254eff083`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl:116:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'prepares DllMain handoff after TLS ordering without executing DllMain' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB loader-lock readiness before the retained DllMain handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB memory writes before the retained DllMain handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB layout records before the retained DllMain handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
