# Simpleos Wine Dll View Relocation Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_view_relocation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_view_relocation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_view_relocation_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_view_relocation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Relocation Specification

## Scenarios

### REQ-048 SimpleOS Wine DLL view relocations

#### applies DLL view relocations without executing DLL startup code

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val result = wine_dll_apply_file_view_relocations("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability")
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-relocations-applied")
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2100)
expect(result.evidence).to_contain("file-backed-dll-view-persistent")
expect(result.evidence).to_contain("relocation-applied")
expect(result.evidence).to_contain("dll-view-write-window")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.evidence).to_contain("no-tls-callback-executed")
```

</details>

#### applies DLL view relocations only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_apply_file_view_relocations_with_peb_teb_vm_writes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", vm_writes)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-relocations-applied")
expect(result.relocation_count).to_equal(1)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-view-write-window")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-048 SimpleOS Wine DLL view relocations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
