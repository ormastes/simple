# Simpleos Wine Dll Image Map Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_image_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_image_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_image_map_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_image_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll Image Map Specification

## Scenarios

### SimpleOS Wine DLL image map handoff

### REQ-042: modeled DLL image map handoff without DLL execution

#### should map and unmap a searched DLL image through SimpleOS VM evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
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
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.mapped_base).to_equal(0x70000000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("NtCreateSection NtMapViewOfSection NtUnmapViewOfSection")
expect(result.evidence).to_contain("os-vma")
expect(result.evidence).to_contain("dll-section-created")
expect(result.evidence).to_contain("dll-view-mapped")
expect(result.evidence).to_contain("dll-view-unmapped")
expect(result.evidence).to_contain("no-host-filesystem-access")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.status).to_equal("dll-image-map-handoff-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_image_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine DLL image map handoff
- REQ-042: modeled DLL image map handoff without DLL execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
