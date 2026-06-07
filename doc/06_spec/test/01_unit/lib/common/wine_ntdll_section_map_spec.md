# Wine Ntdll Section Map Specification

> 1. wine ntdll section table new

<!-- sdn-diagram:id=wine_ntdll_section_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_section_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_section_map_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_section_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Section Map Specification

## Scenarios

### Wine NTDLL section map bridge

#### executes a bounded NtCreateSection, NtMapViewOfSection, and NtUnmapViewOfSection sequence

1. wine ntdll section table new
2. wine vm process space new
   - Expected: result.ok is true
   - Expected: result.handle equals `0x400`
   - Expected: result.mapped_base equals `0x400000`
   - Expected: result.table.sections[0].mapped_base equals `0`
   - Expected: result.space.regions.len() equals `0`
   - Expected: result.operations equals `NtCreateSection NtMapViewOfSection NtUnmapViewOfSection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "\\KnownDlls\\kernel32.dll",
    0x3000,
    0x400000
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x400)
expect(result.mapped_base).to_equal(0x400000)
expect(result.table.sections[0].mapped_base).to_equal(0)
expect(result.space.regions.len()).to_equal(0)
expect(result.operations).to_equal("NtCreateSection NtMapViewOfSection NtUnmapViewOfSection")
```

</details>

#### keeps NTDLL section mapping ordered and bounded

1. wine ntdll section table new
2. wine vm process space new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `ntdll-section-map-sequence-expected:NtCreateSection`
3. wine ntdll section table new
4. wine vm process space new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_ntdll_execute_section_map(
    ["NtMapViewOfSection", "NtCreateSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "\\KnownDlls\\kernel32.dll",
    0x3000,
    0x400000
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("ntdll-section-map-sequence-expected:NtCreateSection")

val wrong_family = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtCreateFile"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "\\KnownDlls\\kernel32.dll",
    0x3000,
    0x400000
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### rejects invalid section descriptors and conflicting view bases

1. wine ntdll section table new
2. wine vm process space new
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `NtCreateSection:invalid-name`
3. wine ntdll section table new
   - Expected: conflict.ok is false
   - Expected: conflict.error equals `NtMapViewOfSection:fixed-map-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "",
    0x3000,
    0x400000
)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("NtCreateSection:invalid-name")

val occupied = wine_vm_map_executable_image(wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"), 0x400000, 0x1000)
val conflict = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    occupied.space,
    "\\KnownDlls\\user32.dll",
    0x3000,
    0x400000
)
expect(conflict.ok).to_equal(false)
expect(conflict.error).to_equal("NtMapViewOfSection:fixed-map-conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_section_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL section map bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
