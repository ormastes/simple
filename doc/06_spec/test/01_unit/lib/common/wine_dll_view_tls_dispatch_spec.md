# Wine Dll View Tls Dispatch Specification

> <details>

<!-- sdn-diagram:id=wine_dll_view_tls_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_view_tls_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_view_tls_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_view_tls_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Tls Dispatch Specification

## Scenarios

### wine dll view TLS dispatch

#### records TLS callback dispatch after import binding without executing callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_record_file_view_tls_dispatch("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-tls-dispatch-recorded")
expect(result.callback_count).to_equal(1)
expect(result.first_callback_rva).to_equal(0x2100)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("dll-import-thunk-bytes-written")
expect(result.evidence).to_contain("tls-callback-dispatch")
expect(result.evidence).to_contain("tls-before-dllmain")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### keeps TLS planning behind callback support evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_record_file_view_tls_dispatch("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("dll-tls:missing-api-tls-callback")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_view_tls_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll view TLS dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
