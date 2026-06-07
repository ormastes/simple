# Wine Pe Loader Runtime Specification

> <details>

<!-- sdn-diagram:id=wine_pe_loader_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_pe_loader_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_pe_loader_runtime_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_pe_loader_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Pe Loader Runtime Specification

## Scenarios

### Wine PE loader runtime evidence

#### plans a bounded DIR64 relocation from a mapped relocation block

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_pe_apply_relocation_plan(_image(), 0x400000, 0x500000)
expect(result.ok).to_equal(true)
expect(result.delta).to_equal(0x100000)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2018)
expect(result.operations).to_equal("relocation-directory relocation-block relocation-dir64 relocation-applied")
```

</details>

#### rejects unsupported relocation types and unmapped targets

1. var bad type =  image
2. bad type =  put u16 le
   - Expected: wine_pe_apply_relocation_plan(bad_type, 0x400000, 0x500000).error equals `relocation-type-unsupported`
3. var unmapped =  image
4. unmapped =  put u16 le
   - Expected: wine_pe_apply_relocation_plan(unmapped, 0x400000, 0x500000).error equals `relocation-target-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad_type = _image()
bad_type = _put_u16_le(bad_type, 0x368, 0x3018)
expect(wine_pe_apply_relocation_plan(bad_type, 0x400000, 0x500000).error).to_equal("relocation-type-unsupported")

var unmapped = _image()
unmapped = _put_u16_le(unmapped, 0x368, 0xa900)
expect(wine_pe_apply_relocation_plan(unmapped, 0x400000, 0x500000).error).to_equal("relocation-target-unmapped")
```

</details>

#### plans TLS callback dispatch only with dynamic-loader callback support

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked = wine_pe_tls_callback_plan(_image(), "native-module-open")
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("missing-api-tls-callback")

val result = wine_pe_tls_callback_plan(_image(), "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.callback_count).to_equal(1)
expect(result.first_callback_rva).to_equal(0x2010)
expect(result.operations).to_equal("tls-directory tls-callback-table tls-callback-dispatch")
```

</details>

#### accepts an empty TLS callback table as explicit loader evidence

1. var empty =  image
2. empty =  put u32 le
   - Expected: result.ok is true
   - Expected: result.callback_count equals `0`
   - Expected: result.operations equals `tls-directory tls-callback-table-empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty = _image()
empty = _put_u32_le(empty, 0x390, 0)
val result = wine_pe_tls_callback_plan(empty, "tls-callback")
expect(result.ok).to_equal(true)
expect(result.callback_count).to_equal(0)
expect(result.operations).to_equal("tls-directory tls-callback-table-empty")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_pe_loader_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine PE loader runtime evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
