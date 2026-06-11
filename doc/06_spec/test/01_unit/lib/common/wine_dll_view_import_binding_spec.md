# Wine Dll View Import Binding Specification

> <details>

<!-- sdn-diagram:id=wine_dll_view_import_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_view_import_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_view_import_binding_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_view_import_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Import Binding Specification

## Scenarios

### wine dll view import binding

#### patches modeled import addresses through a retained relocated DLL view

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_and_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_bind_file_view_imports("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-imports-bound")
expect(result.mapped_base).to_equal(0x500000)
expect(result.module_count).to_equal(1)
expect(result.resolved_count).to_equal(1)
expect(result.patched_count).to_equal(1)
expect(result.first_iat_rva).to_equal(0x2080)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2080))).to_equal(0x120006)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2100))).to_equal(0x501234)
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-import-thunk-bytes-written")
expect(result.evidence).to_contain("dll-view-rx-restored")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### rejects unsupported DLL imports before opening the import write window

1. var data =  dll with import and relocation
2. data =  put ascii z
   - Expected: result.ok is false
   - Expected: result.error equals `unsupported-import-module:missing.dll`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = _dll_with_import_and_relocation()
data = _put_ascii_z(data, 0x250, "missing.dll")
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_bind_file_view_imports("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-import-module:missing.dll")
expect(result.evidence).to_contain("no-dll-iat-written")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_view_import_binding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll view import binding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
