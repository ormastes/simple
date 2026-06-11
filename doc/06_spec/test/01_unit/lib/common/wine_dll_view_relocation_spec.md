# Wine Dll View Relocation Specification

> <details>

<!-- sdn-diagram:id=wine_dll_view_relocation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_view_relocation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_view_relocation_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_view_relocation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Relocation Specification

## Scenarios

### wine dll view relocation

#### applies a bounded DIR64 relocation through a retained DLL view write window

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_dir64_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val result = wine_dll_apply_file_view_relocations("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability")
expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x500000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2100)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2100))).to_equal(0x501234)
expect(result.evidence).to_contain("file-backed-dll-view-persistent")
expect(result.evidence).to_contain("relocation-dir64")
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-view-rx-restored")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### applies retained DLL view relocations only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_dir64_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_apply_file_view_relocations_with_peb_teb_vm_writes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", vm_writes)
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

#### rejects missing relocation directories before mutating the DLL image

1. var data =  dll with dir64 relocation
2. data =  put u32 le
3. data =  put u32 le
   - Expected: result.ok is false
   - Expected: result.error equals `relocation:missing-relocation-directory`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _dll_with_dir64_relocation()
data = _put_u32_le(data, 0x98 + 0x70 + 40, 0)
data = _put_u32_le(data, 0x98 + 0x70 + 44, 0)
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val result = wine_dll_apply_file_view_relocations("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("relocation:missing-relocation-directory")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_view_relocation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll view relocation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
