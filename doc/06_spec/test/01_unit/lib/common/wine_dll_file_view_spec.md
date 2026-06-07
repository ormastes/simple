# Wine Dll File View Specification

> <details>

<!-- sdn-diagram:id=wine_dll_file_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_file_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_file_view_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_file_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll File View Specification

## Scenarios

### wine dll file view

#### maps a validated DLL file probe into a persistent process image view

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", _dll_bytes())]
val result = wine_dll_map_file_backed_view("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, 33, 44, "pid fs ipc net capability", 0x79000000)
expect(result.ok).to_equal(true)
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.mapped_base).to_equal(0x79000000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.entrypoint_rva).to_equal(0x1200)
expect(result.status).to_equal("dll-file-backed-view-mapped")
val region = wine_vm_space_find(result.space, 0x79000000)
expect(region.kind).to_equal("image")
expect(region.perms).to_equal("rx")
expect(result.evidence).to_contain("dll-file-probe-validated")
expect(result.evidence).to_contain("file-backed-dll-view-persistent")
expect(result.evidence).to_contain("os-vma")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### maps a retained DLL file view only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", _dll_bytes())]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_map_file_backed_view_with_peb_teb_vm_writes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, 33, 44, "pid fs ipc net capability", 0x79000000, vm_writes)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-file-backed-view-mapped")
expect(result.mapped_base).to_equal(0x79000000)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("file-backed-dll-view-mapped")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### rejects invalid probe or mapping inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid_base = wine_dll_map_file_backed_view("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], [], 33, 44, "pid fs ipc net capability", 0)
expect(invalid_base.ok).to_equal(false)
expect(invalid_base.error).to_equal("invalid-image-base")
val missing = wine_dll_map_file_backed_view("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", [], [], [], 33, 44, "pid fs ipc net capability", 0x79000000)
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("dll-file-probe:dll-file-not-found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_file_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll file view

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
