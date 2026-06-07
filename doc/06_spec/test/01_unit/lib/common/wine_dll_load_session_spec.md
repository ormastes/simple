# Wine Dll Load Session Specification

> <details>

<!-- sdn-diagram:id=wine_dll_load_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_load_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_load_session_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_load_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll Load Session Specification

## Scenarios

### wine dll load session

#### records modeled loaded image state after image-map handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x71000000)
val result = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", ["D:\\GameBin"], ["kernel32.dll"], 0x6000)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.mapped_base).to_equal(0x71000000)
expect(result.mapped_size).to_equal(0x6000)
expect(result.ref_count).to_equal(1)
expect(result.status).to_equal("dll-load-session-recorded")
expect(wine_dll_load_session_loaded_count(result.session)).to_equal(1)
expect(result.evidence).to_contain("dll-image-map-handoff-ready")
expect(result.evidence).to_contain("dll-load-session-recorded")
expect(result.evidence).to_contain("modeled-loaded-image")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.evidence).to_contain("no-tls-callback-executed")
```

</details>

#### increments modeled refcount for repeated loads and unloads by refcount

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x72000000)
val first = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x5000)
val second = wine_dll_session_load_modeled(first.session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x5000)
expect(second.ok).to_equal(true)
expect(second.ref_count).to_equal(2)
expect(second.status).to_equal("dll-load-existing-refcounted")
expect(wine_dll_load_session_loaded_count(second.session)).to_equal(1)
val released = wine_dll_session_unload_modeled(second.session, "kernel32.dll")
expect(released.ok).to_equal(true)
expect(released.ref_count).to_equal(1)
expect(wine_dll_load_session_loaded_count(released.session)).to_equal(1)
```

</details>

#### rolls back modeled loads without leaving loaded state

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x73000000)
val result = wine_dll_session_load_with_rollback(session, "user32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x7000, false)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("dll-load-session-rolled-back")
expect(result.status).to_equal("rolled-back")
expect(result.ref_count).to_equal(0)
expect(wine_dll_load_session_loaded_count(result.session)).to_equal(0)
expect(result.evidence).to_contain("dll-load-session-unloaded")
expect(result.evidence).to_contain("dll-load-session-rolled-back")
expect(result.evidence).to_contain("no-real-dll-loaded")
```

</details>

#### rejects invalid image handoff inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x74000000)
val result = wine_dll_session_load_modeled(session, "C:\\Windows\\kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x4000)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("image-map:dll-search:dll-name-must-be-basename")
expect(result.status).to_equal("rejected")
expect(wine_dll_load_session_loaded_count(result.session)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_load_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll load session

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
