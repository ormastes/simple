# Simpleos Wine Dll View Startup Fault Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_view_startup_fault_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_view_startup_fault_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_view_startup_fault_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_view_startup_fault_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Startup Fault Specification

## Scenarios

### REQ-044: DLL view startup fault rollback

#### records SEH rollback around DllMain startup while keeping DLL code non-executing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x502100, access: "execute", policy: "deliver-seh")
val result = wine_dll_record_file_view_startup_fault("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", fault)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-startup-fault-rollback-recorded")
expect(result.rollback_count).to_equal(1)
expect(result.evidence).to_contain("seh-dispatch-recorded")
expect(result.evidence).to_contain("loader-lock-released")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### requires PEB/TEB write-gated DllMain handoff before startup rollback

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
