# Wine Pe Loader Specification

> <details>

<!-- sdn-diagram:id=wine_pe_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_pe_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_pe_loader_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_pe_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Pe Loader Specification

## Scenarios

### Wine PE/DLL loader

#### applies DIR64 relocations with full block iteration and verifies patched values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _reloc_image()
val result = wine_pe_apply_all_relocations(image, 0x400000, 0x500000)
expect(result.ok).to_equal(true)
expect(result.delta).to_equal(0x100000)
expect(result.relocation_count).to_equal(2)
expect(result.operations).to_contain("relocation-all-applied")
```

</details>

#### applies relocations to image bytes and verifies patched u64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _reloc_image()
val patched = wine_pe_apply_all_relocations_to_image(image, 0x400000, 0x500000)
val val1 = _read_u64_le(patched, 0x218)
val val2 = _read_u64_le(patched, 0x228)
expect(val1).to_equal(0x500100)
expect(val2).to_equal(0x500200)
```

</details>

#### skips ABSOLUTE (type 0) relocation entries

1. var image =  reloc image
2. image =  put u16 le
   - Expected: result.ok is true
   - Expected: result.relocation_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var image = _reloc_image()
image = _put_u16_le(image, 0x36a, 0x0028)
val result = wine_pe_apply_all_relocations(image, 0x400000, 0x500000)
expect(result.ok).to_equal(true)
expect(result.relocation_count).to_equal(1)
```

</details>

#### handles empty relocation directory with zero delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _reloc_image()
val result = wine_pe_apply_all_relocations(image, 0x400000, 0x400000)
expect(result.ok).to_equal(true)
expect(result.relocation_count).to_equal(0)
expect(result.operations).to_contain("relocation-delta-zero")
```

</details>

#### looks up PE exports by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _export_image()
val alpha_rva = pe_export_lookup_by_name(image, "Alpha")
expect(alpha_rva).to_equal(0x2010)
val beta_rva = pe_export_lookup_by_name(image, "Beta")
expect(beta_rva).to_equal(0x2030)
```

</details>

#### returns -1 for unknown export name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _export_image()
val missing = pe_export_lookup_by_name(image, "NonExistent")
expect(missing).to_equal(-1)
```

</details>

#### maps PE image with correct size and section count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _reloc_image()
val mapped = wine_dll_map_pe_image(image, 0x400000)
expect(mapped.ok).to_equal(true)
expect(mapped.image_size).to_equal(0x5000)
expect(mapped.section_count).to_equal(1)
expect(mapped.entry_point_rva).to_equal(0x2010)
expect(mapped.image.len()).to_equal(0x5000)
```

</details>

#### maps PE image at different base and applies relocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _reloc_image()
val mapped = wine_dll_map_pe_image(image, 0x500000)
expect(mapped.ok).to_equal(true)
expect(mapped.preferred_base).to_equal(0x400000)
expect(mapped.load_base).to_equal(0x500000)
expect(mapped.relocation_count).to_equal(2)
```

</details>

#### records DllMain invocation without executing native code

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = wine_dll_invoke_dllmain("test.dll", 0x400000, 0x2010, 0, 1, 0, "modeled-loaded-image")
expect(record.ok).to_equal(true)
expect(record.dll_name).to_equal("test.dll")
expect(record.h_instance).to_equal(0x400000)
expect(record.reason).to_equal(1)
expect(record.invoked).to_equal(false)
expect(record.evidence).to_contain("DllMain-invocation-recorded")
expect(record.evidence).to_contain("DLL_PROCESS_ATTACH")
expect(record.evidence).to_contain("invocation-deferred-pending-rt_dyncall_3")
```

</details>

#### rejects DllMain invocation with invalid parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_name = wine_dll_invoke_dllmain("", 0x400000, 0x2010, 0, 1, 0, "")
expect(no_name.ok).to_equal(false)
expect(no_name.error).to_equal("missing-dll-name")

val no_base = wine_dll_invoke_dllmain("test.dll", 0, 0x2010, 0, 1, 0, "")
expect(no_base.ok).to_equal(false)
expect(no_base.error).to_equal("invalid-image-base")

val bad_reason = wine_dll_invoke_dllmain("test.dll", 0x400000, 0x2010, 0, 5, 0, "")
expect(bad_reason.ok).to_equal(false)
expect(bad_reason.error).to_equal("unsupported-reason")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_pe_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine PE/DLL loader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
