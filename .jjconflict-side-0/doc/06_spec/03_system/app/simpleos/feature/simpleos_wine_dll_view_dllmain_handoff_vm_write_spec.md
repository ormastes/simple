# Simpleos Wine Dll View Dllmain Handoff Vm Write Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_view_dllmain_handoff_vm_write_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_view_dllmain_handoff_vm_write_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_view_dllmain_handoff_vm_write_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_view_dllmain_handoff_vm_write_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Dllmain Handoff Vm Write Specification

## Scenarios

### SimpleOS Wine DLL view DllMain handoff VM writes

#### should prepare retained DllMain handoff only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_prepare_file_view_dllmain_handoff_with_peb_teb_vm_writes("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", vm_writes)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.entrypoint_address).to_equal(0x502100)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("PEBTEBLayoutVMReadback")
expect(result.evidence).to_contain("dll-view-imports-bound")
expect(result.evidence).to_contain("dllmain-process-attach-planned")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_vm_write_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine DLL view DllMain handoff VM writes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
