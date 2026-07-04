# Simpleos Wine Dll Load Session Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_load_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_load_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_load_session_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_load_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll Load Session Specification

## Scenarios

### REQ-043 SimpleOS Wine modeled DLL load session

#### records load state and rollback evidence without executing DLL code

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x75000000)
val committed = wine_dll_session_load_with_rollback(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", ["D:\\GameBin"], ["kernel32.dll"], 0x6000, true)
expect(committed.ok).to_equal(true)
expect(committed.status).to_equal("dll-load-session-recorded")
expect(wine_dll_load_session_loaded_count(committed.session)).to_equal(1)
expect(committed.evidence).to_contain("dll-image-map-handoff-ready")
expect(committed.evidence).to_contain("modeled-loaded-image")
expect(committed.evidence).to_contain("no-real-dll-loaded")
expect(committed.evidence).to_contain("no-dll-entrypoint-executed")
expect(committed.evidence).to_contain("no-tls-callback-executed")

val rolled = wine_dll_session_load_with_rollback(committed.session, "user32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x7000, false)
expect(rolled.ok).to_equal(false)
expect(rolled.status).to_equal("rolled-back")
expect(wine_dll_load_session_loaded_count(rolled.session)).to_equal(1)
expect(rolled.evidence).to_contain("dll-load-session-rolled-back")
expect(rolled.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_load_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-043 SimpleOS Wine modeled DLL load session

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
