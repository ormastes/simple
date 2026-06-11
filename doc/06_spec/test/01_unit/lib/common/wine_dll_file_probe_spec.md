# Wine Dll File Probe Specification

> <details>

<!-- sdn-diagram:id=wine_dll_file_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_file_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_file_probe_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_file_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll File Probe Specification

## Scenarios

### wine dll file probe

#### selects the first existing search-order candidate and validates its bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [wine_dll_probe_file("C:\\Games\\gameaudio.dll", _dll_bytes())]
val result = wine_dll_probe_candidate_bytes("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", ["D:\\GameBin"], ["kernel32.dll"], files)
expect(result.ok).to_equal(true)
expect(result.selected_path).to_equal("C:\\Games\\gameaudio.dll")
expect(result.image_size).to_equal(0x5000)
expect(result.entrypoint_rva).to_equal(0x1200)
expect(result.status).to_equal("dll-file-probe-validated")
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("dll-file-probe-candidate-found")
expect(result.evidence).to_contain("file-backed-dll-bytes")
expect(result.evidence).to_contain("no-persistent-dll-view")
```

</details>

#### prefers KnownDlls when the known candidate exists

1. wine dll probe file
2. wine dll probe file
   - Expected: result.ok is true
   - Expected: result.selected_path equals `\\KnownDlls\\kernel32.dll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    wine_dll_probe_file("C:\\Games\\kernel32.dll", _dll_bytes()),
    wine_dll_probe_file("\\KnownDlls\\kernel32.dll", _dll_bytes())
]
val result = wine_dll_probe_candidate_bytes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files)
expect(result.ok).to_equal(true)
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
```

</details>

#### rejects missing files and malformed candidate bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_dll_probe_candidate_bytes("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", [], [], [])
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("dll-file-not-found")
val bad = wine_dll_probe_candidate_bytes("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", [], [], [wine_dll_probe_file("C:\\Games\\gameaudio.dll", [1, 2, 3])])
expect(bad.ok).to_equal(false)
expect(bad.error).to_equal("dll-bytes:dll-bytes-too-small")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_file_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll file probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
