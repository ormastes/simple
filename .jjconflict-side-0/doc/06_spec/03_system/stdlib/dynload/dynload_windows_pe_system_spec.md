# Dynload Windows Pe System Specification

> <details>

<!-- sdn-diagram:id=dynload_windows_pe_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynload_windows_pe_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynload_windows_pe_system_spec -> std
dynload_windows_pe_system_spec -> common
dynload_windows_pe_system_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynload_windows_pe_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynload Windows Pe System Specification

## Scenarios

### Dynload Windows PE System

### PE image parsing

#### reads PE image base and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_reloc_image()
val base = pe_image_base(img)
expect(base).to_equal(0x400000)
val size = pe_size_of_image(img)
expect(size).to_equal(0x5000)
```

</details>

### relocation

#### applies DIR64 relocations with correct delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_reloc_image()
val result = wine_pe_apply_all_relocations(img, 0x400000, 0x500000)
expect(result.ok).to_equal(true)
expect(result.relocation_count).to_equal(2)
```

</details>

#### handles zero-delta relocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_reloc_image()
val result = wine_pe_apply_all_relocations(img, 0x400000, 0x400000)
expect(result.ok).to_equal(true)
expect(result.relocation_count).to_equal(0)
expect(result.operations).to_contain("relocation-delta-zero")
```

</details>

### export resolution

#### resolves named exports from PE export directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_export_image()
val alpha = pe_export_lookup_by_name(img, "Alpha")
expect(alpha).to_equal(0x2010)
val beta = pe_export_lookup_by_name(img, "Beta")
expect(beta).to_equal(0x2030)
```

</details>

#### returns -1 for unknown export name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_export_image()
val missing = pe_export_lookup_by_name(img, "NonExistent")
expect(missing).to_equal(-1)
```

</details>

### image mapping

#### maps PE image with correct size and sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_reloc_image()
val mapped = wine_dll_map_pe_image(img, 0x400000)
expect(mapped.ok).to_equal(true)
expect(mapped.image_size).to_equal(0x5000)
expect(mapped.section_count).to_equal(1)
expect(mapped.entry_point_rva).to_equal(0x2010)
```

</details>

#### maps PE image at different base and applies relocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_pe64_reloc_image()
val mapped = wine_dll_map_pe_image(img, 0x500000)
expect(mapped.ok).to_equal(true)
expect(mapped.preferred_base).to_equal(0x400000)
expect(mapped.load_base).to_equal(0x500000)
expect(mapped.relocation_count).to_equal(2)
```

</details>

### DllMain lifecycle

#### records DllMain invocation for DLL_PROCESS_ATTACH

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = wine_dll_invoke_dllmain("test.dll", 0x400000, 0x2010, 0, 1, 0, "system-test")
expect(record.ok).to_equal(true)
expect(record.dll_name).to_equal("test.dll")
expect(record.reason).to_equal(1)
expect(record.invoked).to_equal(false)
expect(record.evidence).to_contain("DllMain-invocation-recorded")
expect(record.evidence).to_contain("DLL_PROCESS_ATTACH")
```

</details>

#### rejects DllMain with invalid parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_name = wine_dll_invoke_dllmain("", 0x400000, 0x2010, 0, 1, 0, "")
expect(no_name.ok).to_equal(false)
expect(no_name.error).to_equal("missing-dll-name")
val no_base = wine_dll_invoke_dllmain("test.dll", 0, 0x2010, 0, 1, 0, "")
expect(no_base.ok).to_equal(false)
expect(no_base.error).to_equal("invalid-image-base")
```

</details>

### windows-only tests

#### verifies PE loading on native Windows

1. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    val img = make_pe64_reloc_image()
    val mapped = wine_dll_map_pe_image(img, 0x400000)
    expect(mapped.ok).to_equal(true)
    expect(mapped.image_size).to_equal(0x5000)
else:
    print("SKIP: Windows-native PE load (not on Windows)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/dynload/dynload_windows_pe_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dynload Windows PE System
- PE image parsing
- relocation
- export resolution
- image mapping
- DllMain lifecycle
- windows-only tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
