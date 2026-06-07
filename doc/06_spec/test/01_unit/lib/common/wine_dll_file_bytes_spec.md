# Wine Dll File Bytes Specification

> <details>

<!-- sdn-diagram:id=wine_dll_file_bytes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_file_bytes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_file_bytes_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_file_bytes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll File Bytes Specification

## Scenarios

### wine dll file bytes

#### validates supplied file-backed PE DLL bytes before persistent mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", _minimal_dll_bytes())
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.byte_count).to_equal(1024)
expect(result.image_size).to_equal(0x5000)
expect(result.entrypoint_rva).to_equal(0x1200)
expect(result.status).to_equal("dll-file-bytes-validated")
expect(result.evidence).to_contain("file-backed-dll-bytes")
expect(result.evidence).to_contain("pe-dll-characteristic")
expect(result.evidence).to_contain("no-persistent-dll-view")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### rejects non-DLL PE images and malformed byte buffers

1. var exe =  minimal dll bytes
2. exe =  put u16 le
   - Expected: non_dll.ok is false
   - Expected: non_dll.error equals `pe-image-is-not-dll`
   - Expected: bad.error equals `dll-bytes-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exe = _minimal_dll_bytes()
exe = _put_u16_le(exe, 0x96, 0x0022)
val non_dll = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", exe)
expect(non_dll.ok).to_equal(false)
expect(non_dll.error).to_equal("pe-image-is-not-dll")
val bad = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", [1, 2, 3])
expect(bad.error).to_equal("dll-bytes-too-small")
```

</details>

#### requires selected path and DLL entrypoint metadata

1. var missing entry =  minimal dll bytes
2. missing entry =  put u32 le
   - Expected: result.error equals `missing-dll-entrypoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = wine_dll_validate_file_bytes("kernel32.dll", "", _minimal_dll_bytes())
expect(missing_path.error).to_equal("missing-selected-path")
var missing_entry = _minimal_dll_bytes()
missing_entry = _put_u32_le(missing_entry, 0x98 + 0x10, 0)
val result = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", missing_entry)
expect(result.error).to_equal("missing-dll-entrypoint")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_file_bytes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll file bytes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
