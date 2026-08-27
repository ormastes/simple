# Simpleos Wine Dll File View Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_file_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_file_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_file_view_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_file_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll File View Specification

## Scenarios

### REQ-047 SimpleOS Wine DLL file-backed view

#### maps validated DLL bytes into a retained non-executing process view

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", _dll_bytes())]
val result = wine_dll_map_file_backed_view("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, 45, 46, "pid fs ipc net capability", 0x7a000000)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-file-backed-view-mapped")
expect(result.mapped_base).to_equal(0x7a000000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.evidence).to_contain("file-backed-dll-bytes")
expect(result.evidence).to_contain("file-backed-dll-view-persistent")
expect(result.evidence).to_contain("image-map")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.evidence).to_contain("no-tls-callback-executed")
```

</details>

#### maps validated DLL bytes only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", _dll_bytes())]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_map_file_backed_view_with_peb_teb_vm_writes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, 45, 46, "pid fs ipc net capability", 0x7a000000, vm_writes)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-file-backed-view-mapped")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("file-backed-dll-view-mapped")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_file_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-047 SimpleOS Wine DLL file-backed view

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
