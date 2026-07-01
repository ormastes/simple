# Simpleos Wine Dll View Import Binding Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_view_import_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_view_import_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_view_import_binding_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_view_import_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Import Binding Specification

## Scenarios

### REQ-049 SimpleOS Wine DLL view import binding

#### binds modeled DLL imports after relocation without executing DLL startup code

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_and_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_bind_file_view_imports("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-imports-bound")
expect(result.module_count).to_equal(1)
expect(result.resolved_count).to_equal(1)
expect(result.patched_count).to_equal(1)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2080))).to_equal(0x120006)
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-import-thunk-bytes-written")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.evidence).to_contain("no-tls-callback-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_import_binding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-049 SimpleOS Wine DLL view import binding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
