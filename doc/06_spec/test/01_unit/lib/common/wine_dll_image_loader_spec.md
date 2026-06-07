# Wine Dll Image Loader Specification

> <details>

<!-- sdn-diagram:id=wine_dll_image_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_image_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_image_loader_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_image_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll Image Loader Specification

## Scenarios

### Wine DLL image loader handoff

#### maps and unmaps a modeled KnownDll image without executing DLL code

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_dll_prepare_image_map_handoff(
    "kernel32.dll",
    "C:\\Games",
    "C:\\Users\\Player",
    ["D:\\GameBin"],
    ["kernel32.dll", "ntdll.dll"],
    0x5000,
    0x70000000
)

expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.mapped_base).to_equal(0x70000000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.section_handle).to_equal(0x400)
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("NtCreateSection NtMapViewOfSection NtUnmapViewOfSection")
expect(result.evidence).to_contain("dll-image-map-handoff-ready")
expect(result.evidence).to_contain("dll-view-unmapped")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.status).to_equal("dll-image-map-handoff-ready")
```

</details>

#### rejects invalid image map parameters before section mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_size = wine_dll_prepare_image_map_handoff("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0, 0x70000000)
expect(bad_size.ok).to_equal(false)
expect(bad_size.error).to_equal("invalid-image-size")
expect(bad_size.status).to_equal("rejected")

val bad_base = wine_dll_prepare_image_map_handoff("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x5000, 0)
expect(bad_base.ok).to_equal(false)
expect(bad_base.error).to_equal("invalid-image-base")
expect(bad_base.status).to_equal("rejected")
```

</details>

#### rejects DLL names outside the modeled basename search lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_dll_prepare_image_map_handoff("C:\\Windows\\System32\\kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x5000, 0x70000000)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("dll-search:dll-name-must-be-basename")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_image_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine DLL image loader handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
