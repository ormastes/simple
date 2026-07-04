# Simpleos Wine Dll File Probe Specification

> 1. wine dll probe file

<!-- sdn-diagram:id=simpleos_wine_dll_file_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_file_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_file_probe_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_file_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll File Probe Specification

## Scenarios

### REQ-046 SimpleOS Wine DLL file probe

#### probes DLL search candidates and validates file-backed bytes before mapping

1. wine dll probe file
2. wine dll probe file
   - Expected: result.ok is true
   - Expected: result.selected_path equals `D:\\GameBin\\gameaudio.dll`
   - Expected: result.status equals `dll-file-probe-validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    wine_dll_probe_file("D:\\GameBin\\gameaudio.dll", _dll_bytes()),
    wine_dll_probe_file("C:\\Games\\other.dll", _dll_bytes())
]
val result = wine_dll_probe_candidate_bytes("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", ["D:\\GameBin"], ["kernel32.dll"], files)
expect(result.ok).to_equal(true)
expect(result.selected_path).to_equal("D:\\GameBin\\gameaudio.dll")
expect(result.status).to_equal("dll-file-probe-validated")
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("dll-file-probe-validated")
expect(result.evidence).to_contain("file-backed-dll-bytes")
expect(result.evidence).to_contain("no-persistent-dll-view")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_file_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-046 SimpleOS Wine DLL file probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
