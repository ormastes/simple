# Simpleos Wine Dll View Tls Dispatch Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_view_tls_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_view_tls_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_view_tls_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_view_tls_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Tls Dispatch Specification

## Scenarios

### REQ-050 SimpleOS Wine DLL view TLS dispatch

#### records TLS dispatch order after DLL import binding without executing callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_record_file_view_tls_dispatch("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-tls-dispatch-recorded")
expect(result.callback_count).to_equal(1)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("dll-import-thunk-bytes-written")
expect(result.evidence).to_contain("tls-before-dllmain")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_tls_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-050 SimpleOS Wine DLL view TLS dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
